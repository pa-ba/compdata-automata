{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Automata
-- Copyright   :  (c) 2010-2012 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines stateful term homomorphisms. This (slightly
-- oxymoronic) notion extends per se stateless term homomorphisms with
-- a state that is maintained separately by a bottom-up or top-down
-- state transformation. Additionally, this module also provides
-- combinators to run state transformations themselves.
--
-- Like regular term homomorphisms also stateful homomorphisms (as
-- well as transducers) can be lifted to annotated signatures
-- (cf. "Data.Comp.Annotation").
--
-- The recursion schemes provided in this module are derived from tree
-- automata. They allow for a higher degree of modularity and make it
-- possible to apply fusion. The implementation is based on the paper
-- /Modular Tree Automata/ (Mathematics of Program Construction,
-- 263-299, 2012, <http://dx.doi.org/10.1007/978-3-642-31113-0_14>).
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.Automata
    (
    -- * Stateful Term Homomorphisms
      QHom
    --, below
    --, above
    , pureHom
    , StateAnn (StateAnn)
    -- ** Bottom-Up State Propagation
    , upTrans
    , runUpHom
    , runUpHomSt
    -- ** Top-Down State Propagation
    , downTrans
    , runDownHom
    -- ** Bidirectional State Propagation
    --, runQHom
    -- * Deterministic Bottom-Up Tree Transducers
    , UpTrans
    , UpTrans'
    , mkUpTrans
    , runUpTrans
    , compUpTrans
    , compUpTransHom
    , compHomUpTrans
    , compUpTransSig
    , compSigUpTrans
    , compAlgUpTrans
    -- * Deterministic Bottom-Up Tree State Transformations
    -- ** Monolithic State
    , UpState
    , tagUpState
    , runUpState
    , prodUpState
    -- ** Modular State
    , DUpState
    , dUpState
    , upState
    , runDUpState
    , prodDUpState
    , (|*|)
    -- * Deterministic Top-Down Tree Transducers
    , DownTrans
    , DownTrans'
    , mkDownTrans
    , runDownTrans
    , compDownTrans
    , compDownTransSig
    , compSigDownTrans
    , compDownTransHom
    , compHomDownTrans
    -- * Deterministic Top-Down Tree State Transformations
    -- ** Monolithic State
    , DownState
    , tagDownState
    , prodDownState
    , (:->:) (appHFun)
    -- ** Modular State
    , DDownState
    , dDownState
    , downState
    , prodDDownState
    , (>*<)
    -- * Bidirectional Tree State Transformations
    --, runDState
    -- * Operators for Finite Mappings
    , (&)
    , (|->)
    , empty
    -- * Product State Spaces
    , module Data.Comp.Projection
    -- * Annotations
    , propAnnQ
    , propAnnUp
    , propAnnDown
    , pathAnn
    ) where

import Data.Comp.Multi.HFunctor
import Data.Comp.Param.Multi
import Data.Comp.Param.Multi.HDitraversable
import Data.Comp.Projection
import Data.Comp.Param.Multi.Mapping

import qualified Data.Comp.Ops as O
import Data.Bifunctor (first, second, bimap)
import GHC.Exts (Any)
import Unsafe.Coerce





{-
-- | This function provides access to components of the states from
-- "below".

below :: (?below :: a -> q, p :< q) => a -> p
below = pr . ?below

-- | This function provides access to components of the state from
-- "above"

above :: (?above :: q, p :< q) => p
above = pr ?above

-- | Turns the explicit parameters @?above@ and @?below@ into explicit
-- ones.

explicit :: ((?above :: q, ?below :: b -> q) => c) -> q -> (b -> q) -> c
explicit x ab be = x where ?above = ab; ?below = be
-}

-- | This type represents stateful term homomorphisms. Stateful term
-- homomorphisms have access to a state that is provided (separately)
-- by a bottom-up or top-down state transformation function (or both).

type QHom f q g = forall a b q . q -> (b :=> q) -> f a b :-> Context g a b

-- | This function turns a stateful homomorphism with a fully
-- polymorphic state type into a (stateless) homomorphism.
pureHom :: (forall q . QHom f q g) -> Hom f g
pureHom phom = phom undefined (const undefined)

-- | Annotate a type with a state.
data StateAnn :: * -> (* -> *) -> * -> * where
  StateAnn :: q -> f i -> (StateAnn q f) i

-- | This type represents transition functions of total, deterministic
-- bottom-up tree transducers (UTTs).

type UpTrans f q g = forall a b. f a (StateAnn q b) :-> StateAnn q (Context g a b)


-- | This is a variant of the 'UpTrans' type that makes it easier to
-- define UTTs as it avoids the explicit use of 'Hole' to inject
-- placeholders into the result.

type UpTrans' f q g = forall a b. f a (StateAnn q (Context g a b)) :-> StateAnn q (Context g a b)

-- | This function turns a UTT defined using the type 'UpTrans'' in
-- to the canonical form of type 'UpTrans'.

mkUpTrans :: HDifunctor f => UpTrans' f q g -> UpTrans f q g
mkUpTrans tr t = tr $ hdimap id (\(StateAnn q x) -> StateAnn q $ Hole x) t

-- | This function is aupposed to transform a UTT transition function into an
-- algebra.  I hope it works.

upAlg :: forall f g q . (HDifunctor f, HDifunctor g)  => UpTrans f q g -> Alg f (StateAnn q (Term g))
upAlg trans i = (\(StateAnn x y) -> StateAnn x . unsafeCoerce . appCxt . (unsafeCoerce :: Cxt Hole g a (Cxt NoHole g b c) i -> Cxt Hole g b (Cxt NoHole g b c) i)
                                                 $ hfmapCxt unTerm y)  $ trans i

-- | This function runs the given UTT on the given term.

runUpTrans :: (HDifunctor f, HDifunctor g) => UpTrans f q g -> Term f :-> Term g
runUpTrans trans = (\(StateAnn _ x) -> x) . runUpTransSt trans

-- | This function is a variant of 'runUpTrans' that additionally
-- returns the final state of the run.

runUpTransSt :: (HDifunctor f, HDifunctor g) => UpTrans f q g -> Term f :-> StateAnn q (Term g)
runUpTransSt up = cata (upAlg up)

-- | This function generalises 'runUpTrans' to contexts. Therefore,
-- additionally, a transition function for the holes is needed.

runUpTrans' :: forall f g a b q . (HDifunctor f, HDifunctor g) => UpTrans f q g -> Context f a (StateAnn q b) :-> StateAnn q (Context g a b)
runUpTrans' trans = run where
    run :: Context f a (StateAnn q b) :-> StateAnn q (Context g a b)
    run (Hole (StateAnn q x)) = StateAnn q $ Hole x
    run (Var x) = StateAnn undefined $ Var x
    run (In t) = (\(StateAnn x y) -> StateAnn x $ appCxt y) .  trans $ hdimap id run t

-- | This function composes two UTTs. (see TATA, Theorem 6.4.5)

compUpTrans :: (HDifunctor f, HDifunctor g, HDifunctor h)
               => UpTrans g p h -> UpTrans f q g -> UpTrans f (q,p) h
compUpTrans t2 t1 x = StateAnn (q1,q2) c2 where
    StateAnn q1 c1 = t1 $ hdimap id (\(StateAnn (q1, q2) a) -> StateAnn q1 $ StateAnn q2 a) x
    StateAnn q2 c2 = runUpTrans' t2 c1


-- | This function composes a UTT with an algebra.

compAlgUpTrans :: (HDifunctor f, HDifunctor g)
               => Alg g a -> UpTrans f q g -> Alg f (StateAnn q a)
compAlgUpTrans alg trans = (\(StateAnn x y) -> StateAnn x $ cata' alg y) . trans . hdimap (StateAnn undefined) id


-- | This combinator composes a UTT followed by a signature function.

compSigUpTrans :: (HDifunctor g) => SigFun g h -> UpTrans f q g -> UpTrans f q h
compSigUpTrans sig trans x = StateAnn q $ appSigFun sig x' where
    StateAnn q x' = trans x

-- | This combinator composes a signature function followed by a UTT.

compUpTransSig :: UpTrans g q h -> SigFun f g -> UpTrans f q h
compUpTransSig trans sig = trans . sig

-- | This combinator composes a UTT followed by a homomorphism.

compHomUpTrans :: (HDifunctor g, HDifunctor h) => Hom g h -> UpTrans f q g -> UpTrans f q h
compHomUpTrans hom trans x = StateAnn q $ appHom hom x' where
    StateAnn q x' = trans x

-- | This combinator composes a homomorphism followed by a UTT.

compUpTransHom :: (HDifunctor g, HDifunctor h) => UpTrans g q h -> Hom f g -> UpTrans f q h
compUpTransHom trans hom  = runUpTrans' trans . hom

-- | This type represents transition functions of total, deterministic
-- bottom-up tree acceptors (UTAs).

type UpState f q = Alg f (K q)

-- | Changes the state space of the UTA using the given isomorphism.

tagUpState :: (HDifunctor f) => (K q :=> p) -> (K p :=> q) -> UpState f q -> UpState f p
tagUpState i o s = K . i . s . hdimap (K . i) (K . o)

-- | This combinator runs the given UTA on a term returning the final
-- state of the run.

runUpState :: (HDifunctor f) => UpState f q -> Term f :=> q
runUpState t = (unK .) $ cata t

-- | This function combines the product UTA of the two given UTAs.

prodUpState :: HDifunctor f => UpState f p -> UpState f q -> UpState f (p,q)
prodUpState sp sq t = K (unK p, unK q) where
    p = sp $ hdimap (K . (,undefined) . unK) (K . fst . unK) t
    q = sq $ hdimap (K . (undefined,) . unK) (K . snd . unK) t


-- | This function constructs a UTT from a given stateful term
-- homomorphism with the state propagated by the given UTA.

upTrans :: (HDifunctor f, HDifunctor g) => UpState f q -> QHom f q g -> UpTrans f q g
upTrans st f t = StateAnn (unK q) c
    where q = st $ hdimap (const undefined) (\(StateAnn x _) -> K x) t
          c = hfmapCxt (\(StateAnn _ x) -> x) $ f q (\(StateAnn x _) -> K x) t

-- | This function applies a given stateful term homomorphism with
-- a state space propagated by the given UTA to a term.

runUpHom :: (HDifunctor f, HDifunctor g) => UpState f q -> QHom f q g -> Term f :-> Term g
runUpHom st hom = (\(StateAnn _ x) -> x) . runUpHomSt st hom

-- | This is a variant of 'runUpHom' that also returns the final state
-- of the run.

runUpHomSt :: (HDifunctor f, HDifunctor g) => UpState f q -> QHom f q g -> Term f :-> StateAnn q (Term g)
runUpHomSt alg h = runUpTransSt (upTrans alg h)


-- | This type represents transition functions of generalised
-- deterministic bottom-up tree acceptors (GUTAs) which have access
-- to an extended state space.

type DUpState f p q = (q :< p) => DUpState' f p q
type DUpState' f p q = forall (a :: * -> *) b . p -> (b :=> p) -> f a b :=> q

-- | This combinator turns an arbitrary UTA into a GUTA.

dUpState :: HDifunctor f => UpState f q -> DUpState f p q
dUpState f _ be = unK . f . hdimap (const undefined) (K . pr . be)

-- | This combinator turns a GUTA with the smallest possible state
-- space into a UTA.

upState :: DUpState f q q -> UpState f q
upState f s = K res where res = f res unK s

-- | This combinator runs a GUTA on a term.

runDUpState :: HDifunctor f => DUpState f q q -> Term f :=> q
runDUpState up = runUpState (upState up)

-- | This combinator constructs ahe product of two GUTA.

prodDUpState :: (p :< c, q :< c)
             => DUpState f c p -> DUpState f c q -> DUpState f c (p,q)
prodDUpState sp sq ab be t = (sp ab be t, sq ab be t)

(|*|) :: (p :< c, q :< c)
             => DUpState f c p -> DUpState f c q -> DUpState f c (p,q)
(|*|) = prodDUpState

-- | Newtype wrapper for polymorphic functions, for things that need impredicative polymorphism.
infixr 6 :->:
newtype (q :->: a) i = HFun {appHFun :: q i -> a i}

-- | This type represents transition functions of total deterministic
-- top-down tree transducers (DTTs).

type DownTrans f q g = forall a b i. q -> f a (K q :->: b) i -> Context g a b i


-- | This is a variant of the 'DownTrans' type that makes it easier to
-- define DTTs as it avoids the explicit use of 'Hole' to inject
-- placeholders into the result.

type DownTrans' f q g = forall a b. q -> f a (K q :->: Context g a b) :-> Context g a b

-- | This function turns a DTT defined using the type 'DownTrans'' in
-- to the canonical form of type 'DownTrans'.
mkDownTrans :: HDifunctor f => DownTrans' f q g -> DownTrans f q g
mkDownTrans tr q t = tr q (hdimap id (HFun . (Hole .) . appHFun) t)

-- | This function runs the given DTT on the given tree.

runDownTrans :: forall f g h a b q. (HDifunctor f, HDifunctor g) => DownTrans f q g -> q -> Cxt h f a b :-> Cxt h g a b
runDownTrans tr q t = run t q where
    run :: forall i. Cxt h f a b i -> q -> Cxt h g a b i
    run (In t) q = appCxt $ tr q $ hdimap id (HFun . (. unK) . run) t
    run (Hole a) _ = Hole a
    run (Var a) _ = Var a

-- | This function runs the given DTT on the given tree.
runDownTrans' :: forall f g h a b q . (HDifunctor f, HDifunctor g) => DownTrans f q g -> q -> Cxt h f a (K q :->: b) :-> Cxt h g a b
runDownTrans' tr q t = run t q where
    run :: forall i. Cxt h f a (K q :->: b) i -> q -> Cxt h g a b i
    run (In t) q = appCxt $ tr q $ hdimap id (HFun . (. unK) . run) t
    run (Hole a) q = Hole (appHFun a $ K q)
    run (Var a) _ = Var a


hcurry :: (K (q, p) :->: a) i -> (K q :->: (K p :->: a)) i
hcurry (HFun f) = HFun $ \ (K q) -> HFun $ \ (K p) -> f $ K (q,p)

-- | This function composes two DTTs. (see W.C. Rounds /Mappings and
-- grammars on trees/, Theorem 2.)

compDownTrans :: (HDifunctor f, HDifunctor g, HDifunctor h)
              => DownTrans g p h -> DownTrans f q g -> DownTrans f (q,p) h
compDownTrans t2 t1 (q,p) t = runDownTrans' t2 p $ t1 q (hdimap id hcurry t)



-- | This function composes a signature function after a DTT.

compSigDownTrans :: (HDifunctor g) => SigFun g h -> DownTrans f q g -> DownTrans f q h
compSigDownTrans sig trans q = appSigFun sig . trans q

-- | This function composes a DTT after a function.

compDownTransSig :: DownTrans g q h -> SigFun f g -> DownTrans f q h
compDownTransSig trans hom q t = trans q (hom t)


-- | This function composes a homomorphism after a DTT.

compHomDownTrans :: (HDifunctor g, HDifunctor h)
              => Hom g h -> DownTrans f q g -> DownTrans f q h
compHomDownTrans hom trans q = appHom hom . trans q

-- | This function composes a DTT after a homomorphism.

compDownTransHom :: (HDifunctor g, HDifunctor h)
              => DownTrans g q h -> Hom f g -> DownTrans f q h
compDownTransHom trans hom q t = runDownTrans' trans q (hom t)


-------------------------------------------------------------------------------rewrite

-- | This type represents transition functions of total, deterministic
-- top-down tree acceptors (DTAs).

type DownState (f :: (* -> *) -> (* -> *) -> * -> *) q = forall a b . StateAnn q (f a b) :-> f a (K q)

-- | Changes the state space of the DTA using the given isomorphism.

tagDownState :: HDifunctor f => (q -> p) -> (p -> q) -> DownState f q -> DownState f p
tagDownState i o t (StateAnn q s) = hdimap id (K . i . unK) $ t (StateAnn (o q) s)

class HDizippable (f :: (* -> *) -> (* -> *) -> * -> *) where
    hdizip :: forall a b1 b2 i . f a b1 i -> f a b2 i -> f a (b1 O.:*: b2) i

-- | This function constructs the product DTA of the given two DTAs.

prodDownState :: (HDizippable f, HDifunctor f) => DownState f p -> DownState f q -> DownState f (p,q)
prodDownState sp sq (StateAnn (p,q) t) = hdimap id (\(K p O.:*: K q) -> K (p,q)) $ hdizip (sp (StateAnn p t)) (sq (StateAnn q t))

{-
-- | Apply the given state mapping to the given functorial value by
-- adding the state to the corresponding index if it is in the map and
-- otherwise adding the provided default state.

appMap :: forall f q a b . HDitraversable f => (forall m i . Mapping m i => f a i :=> m q)
                       -> q -> f a (K q :->: b) :-> f a (StateAnn q b)
appMap qmap q s = hdimap id (qfun q) s'
    where s' = number s
          qfun :: forall j . q -> Numbered (K q :->: b) j -> (StateAnn q b) j
          qfun q1 (Numbered i a) = let q' = lookupNumMap q1 i (qmap s')
                                in StateAnn q' . appHFun a $ K q'
-}

-- | This function constructs a DTT from a given stateful term--
-- homomorphism with the state propagated by the given DTA.

downTrans :: forall f g q . (HDizippable f, HDifunctor f, HDifunctor g) => DownState f q -> QHom f q g -> DownTrans f q g
downTrans st f q s = hfmapCxt (\(x O.:*: _) -> x) $ f q (\(_ O.:*: K y) -> y) $ hdimap id (\(h O.:*: q) -> appHFun h q O.:*: q) $ hdizip s $ st $ StateAnn q s


-- | This function applies a given stateful term homomorphism with a
-- state space propagated by the given DTA to a term.

runDownHom :: (HDizippable f, HDifunctor f, HDifunctor g)
            => DownState f q -> QHom f q g -> q -> Term f :-> Term g
runDownHom st h q t = unsafeCoerce . runDownTrans (downTrans st h) q $ unTerm t

-- | This type represents transition functions of generalised
-- deterministic top-down tree acceptors (GDTAs) which have access
-- to an extended state space.
type DDownState f p q = (q :< p) => DDownState' f p q

type DDownState' (f :: (* -> *) -> (* -> *) -> * -> *) p q = forall a i .
                                p -> (i :=> p) -> f a i :-> f a (K q)

-- | This combinator turns an arbitrary DTA into a GDTA.

dDownState :: DownState f q -> DDownState f p q
dDownState f ab _ t = f $ StateAnn (pr ab) t

-- | This combinator turns a GDTA with the smallest possible state
-- space into a DTA.

downState :: forall f q . DDownState f q q -> DownState f q
downState f (StateAnn q s) = res
    where res = f q bel s
          bel _k = error "downstate not implemented" --findWithDefault q k res


-- | This combinator constructs the product of two dependant top-down
-- state transformations.

prodDDownState :: (p :< c, q :< c, HDizippable f, HDifunctor f)
               => DDownState f c p -> DDownState f c q -> DDownState f c (p,q)
prodDDownState sp sq ab be t = hdimap id (\(K p O.:*: K q) -> K (p,q)) $ hdizip (sp ab be t) (sq ab be t)

-- | This is a synonym for 'prodDDownState'.

(>*<) :: (p :< c, q :< c, HDizippable f, HDifunctor f)
         => DDownState f c p -> DDownState f c q -> DDownState f c (p,q)
(>*<) = prodDDownState


{-
-- | This combinator combines a bottom-up and a top-down state
-- transformations. Both state transformations can depend mutually
-- recursive on each other.

runDState :: forall f u d . HDitraversable f => DUpState' f (u,d) u -> DDownState' f (u,d) d -> d -> Term f :=>  u
runDState up down d (Term (In t)) = u where
        t' :: f Any (Numbered (K (u,d))) i
        t' = hdimap id bel . unsafeCoerce $ number t
        bel :: Numbered (Cxt NoHole f Any (K ())) :-> Numbered (K (u, d))
        u = undefined
        bel (Numbered i s) =
            let d' :: d
                d' = lookupNumMap d i m
            in undefined --Numbered i (K $ runDState up down d' (Term $ unsafeCoerce s), d')
        m :: NumMap ((,) u) d
        m = unK $ down (u,d) (bimap unK (const d) . unNumbered) t'
        --u = up (u,d) (bimap unK (const d) . unNumbered) t'
runDState _ _ _ (Term _) = undefined

-- | This combinator runs a stateful term homomorphisms with a state
-- space produced both on a bottom-up and a top-down state
-- transformation.

runQHom :: forall f g u d . (HDitraversable f, HDifunctor g) =>
           DUpState' f (u,d) u -> DDownState' f (u,d) d ->
           QHom f (u,d) g ->
           d -> Term f -> (u, Term g)
runQHom up down trans d (Term (In t)) = (u, Term $ unsafeCoerce t'') where
        t' = dimap id bel $ number t
        bel (Numbered i s) =
            let d' = lookupNumMap d i m
                (u', s') = runQHom up down trans d' (Term $ unsafeCoerce s)
            in Numbered i ((u', d'),s')
        m = explicit down (u,d) (fst . unNumbered) t'
        u = explicit up (u,d) (fst . unNumbered) t'
        t'' = appCxt $ cxtMap (snd . unNumbered) $ cxtMap (fmap (second unTerm)) $ explicit trans (u,d) (fst . unNumbered) t'
runQHom _ _ _ _ (Term _) = undefined
-}

-- | Lift a stateful term homomorphism over signatures @f@ and @g@ to
-- a stateful term homomorphism over the same signatures, but extended with
-- annotations.
propAnnQ :: (DistAnn f p f', DistAnn g p g', HDifunctor g)
        => QHom f q g -> QHom f' q g'
propAnnQ hom ab be f' = ann p (hom ab be f)
    where (f O.:&: p) = projectA f'

-- | Lift a bottom-up tree transducer over signatures @f@ and @g@ to a
-- bottom-up tree transducer over the same signatures, but extended
-- with annotations.
propAnnUp :: (DistAnn f p f', DistAnn g p g', HDifunctor g)
        => UpTrans f q g -> UpTrans f' q g'
propAnnUp trans f' = StateAnn q $ ann p t
    where (f O.:&: p) = projectA f'
          StateAnn q t = trans f

-- | Lift a top-down tree transducer over signatures @f@ and @g@ to a
-- top-down tree transducer over the same signatures, but extended
-- with annotations.
propAnnDown :: (DistAnn f p f', DistAnn g p g', HDifunctor g)
        => DownTrans f q g -> DownTrans f' q g'
propAnnDown trans q f' = ann p (trans q f)
    where (f O.:&: p) = projectA f'


-- | This function adds unique annotations to a term/context. Each
-- node in the term/context is annotated with its path from the root,
-- which is represented as an integer list. It is implemented as a
-- DTT.
pathAnn :: forall g. (HDitraversable g) => CxtFun g (g :&: [Int])
pathAnn = runDownTrans trans [] where
    trans :: DownTrans g [Int] (g :&: [Int])
    trans q t = simpCxt (hdimap id (\ (Numbered n s) -> appHFun s (K $ n:q)) (number t) :&: q)

