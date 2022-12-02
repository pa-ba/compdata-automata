{-# LANGUAGE TemplateHaskell, FlexibleContexts, MultiParamTypeClasses,
TypeOperators, FlexibleInstances, UndecidableInstances,
ScopedTypeVariables, TypeSynonymInstances,
OverlappingInstances, ConstraintKinds, KindSignatures #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Automata.Compiler where

import Data.Comp.Param.Multi.Automata
import Data.Comp.Param.Multi.HDitraversable
import Data.Comp.Multi.HFunctor
--import Data.Comp.Param.Multi.HDifoldable
import Data.Comp.Param.Multi.Derive
import Data.Comp.Param.Multi.Ops
import Data.Comp.Param.Multi hiding (height)
import Data.Foldable
import Prelude hiding (foldl)

import Data.Set (Set, union, singleton, delete, member)
import qualified Data.Set as Set

import Data.Coerce
import Data.Map (Map)
import qualified Data.Map as Map

type Var = String

data Val (a :: * -> *) (b :: * -> *) i where
    Const :: Int -> Val a b Int

data Op (a :: * -> *) b i = Plus (b i) (b i)
            | Times (b i) (b i)

type Core = Op :+: Val

data Let a b i where
    Let :: b i -> (a i -> b j) -> Let a b j

--   deriving HDifunctor
type CoreLet = Let :+: Core

data Sugar (a :: * -> *) b i where
    Neg :: b Int -> Sugar a b i
    Minus :: b Int -> b Int -> Sugar a b Int
--    deriving HDifunctor

$(derive [makeHDifunctor, smartConstructors]
  [''Val, ''Op, ''Let, ''Sugar])


class Eval f where
    evalSt :: UpState f Int

$(derive [liftSum] [''Eval])

instance Eval Val where
    evalSt (Const i) = K i

instance Eval Op where
    evalSt (Plus  x y) = x + y
    evalSt (Times x y) = x * y

instance Eval Let where
    evalSt (Let e f) = f e

type Addr = Int

data Instr = Acc Int
           | Load Addr
           | Store Addr
           | Add Int
           | Sub Int
           | Mul Int
             deriving (Show)

type Code = [Instr]

data MState = MState {
      mRam :: Map Addr Int,
      mAcc :: Int }

runCode :: Code -> MState -> MState
runCode [] = id
runCode (ins:c) = runCode c . step ins
    where step (Acc i) s = s{mAcc = i}
          step (Load a) s = case Map.lookup a (mRam s) of
              Nothing -> error $ "memory cell " ++ show a ++ " is not set"
              Just n -> s {mAcc = n}
          step (Store a) s = s {mRam = Map.insert a (mAcc s) (mRam s)}
          step (Add a) s = exec (+) a s
          step (Sub a) s = exec (-) a s
          step (Mul a) s = exec (*) a s
          exec op a s = case Map.lookup a (mRam s) of
                        Nothing -> error $ "memory cell " ++ show a ++ " is not set"
                        Just n -> s {mAcc = mAcc s `op` n}


runCode' :: Code -> Int
runCode' c = mAcc $ runCode c MState{mRam = Map.empty, mAcc = error "accumulator is not set"}


-- | Defines the height of an expression.
class HasHeight f where
    heightSt :: UpState f Int

$(derive [liftSum] [''HasHeight])

instance HasHeight Val where
    heightSt _ = 0

instance HasHeight Op where
    heightSt (Plus x y) = max x y + 1
    heightSt (Times x y) = max x y + 1

instance HasHeight Let where
    heightSt (Let e f) = f e + 1

tmpAddrSt :: HasHeight f => UpState f Int
tmpAddrSt = (+1) . heightSt


newtype VarAddr = VarAddr {varAddr :: Int} deriving (Eq, Show, Num)

class VarAddrSt f where
  varAddrSt :: DownState f VarAddr

instance (VarAddrSt f, VarAddrSt g) => VarAddrSt (f :+: g) where
    varAddrSt (StateAnn q (Inl x)) = varAddrSt (StateAnn q x)
    varAddrSt (StateAnn q (Inr x)) = varAddrSt (StateAnn q x)

instance VarAddrSt Let where
  varAddrSt (StateAnn d (Let e x)) = x undefined |-> (d + 2)

instance VarAddrSt f where
  varAddrSt _ = empty


{-
type Bind = Map Var Int

bindSt :: (Let :<: f,VarAddr :< q) => DDownState f q Bind
bindSt t = case proj t of
             Just (Let v _ e) -> K $ e |-> q'
                       where q' = Map.insert v (varAddr above) above
             _ -> K empty
-}

-- | Defines the code that an expression is compiled to. It depends on
-- an integer state that denotes the height of the current node.
class CodeSt f q where
    codeSt :: DUpState f q Code

instance (CodeSt f q, CodeSt g q) => CodeSt (f :+: g) q where
    codeSt ab be (Inl x) = codeSt ab be x
    codeSt ab be (Inr x) = codeSt ab be x


instance CodeSt Val q where
    codeSt _ _ (Const i) = [Acc i]

instance (Int :< q) => CodeSt Op q where
    codeSt ab be (Plus x y) = pr (be x) ++ [Store i] ++ pr (be y) ++ [Add i]
        where i = pr $ be y
    codeSt ab be (Times x y) = pr (be x) ++ [Store i] ++ pr (be y) ++ [Mul i]
        where i = pr $ be y

instance (VarAddr :< q) => CodeSt Let q where
    codeSt ab be (Let b e) = pr (be b) ++ [Store i] ++ pr (be (e undefined))
                    where i = varAddr $ pr ab


compile' :: (CodeSt f (Code,Int), HDifunctor f, HasHeight f) => Term f :=> (Code, Int)
compile' = runDUpState (codeSt `prodDUpState` dUpState tmpAddrSt)


exComp' = compile' (Term $ iConst 2 `iPlus` iConst 3 :: Term Core Int)



{-
compile :: (CodeSt f ((Code,Int),VarAddr), HDitraversable f, HDifunctor f, Let :<: f, VarAddrSt f)
           => Term f :=> Code
compile = fst . runDState
          (codeSt `prodDUpState` dUpState tmpAddrSt)
          (bindSt `prodDDownState` dDownState varAddrSt)
          (Map.empty, VarAddr 1)


exComp = compile (iLet "x" (iLet "x" (iConst 5) (iConst 10 `iPlus` iVar "x")) (iConst 2 `iPlus` iVar "x") :: Term CoreLet ())

-- | Defines the set of free variables
class VarsSt f where
    varsSt :: UpState f (Set Var)

$(derive [liftSum] [''VarsSt])

instance VarsSt Val where
    varsSt _ = K Set.empty

instance VarsSt Op where
    varsSt (Plus (K x) (K y)) = K $ x `union` y
    varsSt (Times (K x) (K y)) = K $ x `union` y

instance VarsSt Let where
    varsSt (Var v) = K $ singleton v
    varsSt (Let v (K x) (K y)) = K $ (if v `member` y then x else Set.empty) `union` delete v y

-- | Stateful homomorphism that removes unnecessary let bindings.
remLetHom :: (Set Var :< q, Let :<: f, HFunctor f) => QHom f q f
remLetHom t = case proj t of
                Just (Let v _ y)
                    | not (v `member` below y) -> Hole y
                _ -> simpCxt t

-- | Removes unnecessary let bindings.
remLet :: (Let :<: f, HFunctor f, VarsSt f) => Term f i -> Term f i
remLet = runUpHom varsSt remLetHom

exLet = remLet (iLet "x" (iConst 3) (iConst 2 `iPlus` iVar "y") :: Term CoreLet ())
-}
