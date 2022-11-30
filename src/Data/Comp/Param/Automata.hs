{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}

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

module Data.Comp.Param.Automata
    (
    -- * Stateful Term Homomorphisms
      QHom
    , below
    , above
    , pureHom
    -- ** Bottom-Up State Propagation
    --, upTrans
    --, runUpHom
    --, runUpHomSt
    -- ** Top-Down State Propagation
    --, downTrans
    --, runDownHom
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
    --, dUpState
    --, upState
    --, runDUpState
    --, prodDUpState
    --, (|*|)
    -- * Deterministic Top-Down Tree Transducers
    --, DownTrans
    --, DownTrans'
    --, mkDownTrans
    --, runDownTrans
    --, compDownTrans
    --, compDownTransSig
    --, compSigDownTrans
    --, compDownTransHom
    --, compHomDownTrans
    -- * Deterministic Top-Down Tree State Transformations
    -- ** Monolithic State
    --, DownState
    --, tagDownState
    --, prodDownState
    -- ** Modular State
    --, DDownState
    --, dDownState
    --, downState
    --, prodDDownState
    --, (>*<)
    -- * Bidirectional Tree State Transformations
    --, runDState
    -- * Operators for Finite Mappings
    --, (&)
    --, (|->)
    --, empty
    -- * Product State Spaces
    , module Data.Comp.Projection
    -- * Annotations
    --, propAnnQ
    --, propAnnUp
    --, propAnnDown
    --, pathAnn
    ) where

import Data.Comp.Param.Algebra
import Data.Comp.Param.Difunctor
import Data.Comp.Param.Annotation
import Data.Comp.Projection
--import Data.Comp.Param.Mapping
import Data.Comp.Param.Term

import GHC.Exts (Any)
import Unsafe.Coerce
import Data.Bifunctor (first, second)




-- | This function provides access to components of the states from
-- "below".

below :: (?below :: a -> q, p :< q) => a -> p
below = pr . ?below

-- | This function provides access to components of the states from
-- "woleb".

woleb :: (?woleb :: p -> a, p :< q) => q -> a
woleb = ?woleb . pr

-- | This function provides access to components of the state from
-- "above"

above :: (?above :: q, p :< q) => p
above = pr ?above

-- | Turns the explicit parameters @?above@, @?below, and @?woleb@ into explicit
-- ones.

explicit :: ((?above :: q, ?woleb :: q -> a, ?below :: b -> q') => c) -> q -> (b -> q') -> (q -> a) -> c
explicit x ab be wo = x where ?above = ab;  ?below = be; ?woleb = wo


-- | This type represents stateful term homomorphisms. Stateful term
-- homomorphisms have access to a state that is provided (separately)
-- by a bottom-up or top-down state transformation function (or both).

type QHom f q g = forall a b. (?below :: b -> q, ?woleb :: a -> q, ?above :: q) => f a b -> Context g a b


-- | This function turns a stateful homomorphism with a fully
-- polymorphic state type into a (stateless) homomorphism.
pureHom :: (forall q . QHom f q g) -> Hom f g
pureHom phom t = let ?above = undefined
                     ?below = const undefined
                     ?woleb = const undefined
                 in phom t

-- | This type represents transition functions of total, deterministic
-- bottom-up tree transducers (UTTs).

type UpTrans f q g = forall a b. f a (q,b) -> (q, Context g a b)


-- | This is a variant of the 'UpTrans' type that makes it easier to
-- define UTTs as it avoids the explicit use of 'Hole' to inject
-- placeholders into the result.

type UpTrans' f q g = forall a b. f a (q, Context g a b) -> (q, Context g a b)

-- | This function turns a UTT defined using the type 'UpTrans'' in
-- to the canonical form of type 'UpTrans'.

mkUpTrans :: Difunctor f => UpTrans' f q g -> UpTrans f q g
mkUpTrans tr t = tr $ dimap id (second Hole) t

-- | This function is supposed to transform a UTT transition function into an
-- algebra.  I hope it works.

upAlg :: (Difunctor f, Difunctor g)  => UpTrans f q g -> Alg f (q, Term g)
upAlg trans = (\(x,y) -> (x, Term $ unsafeCoerce y)) . second appCxt . trans . c where
  c :: Difunctor f => f a (q, Term g) -> f Any (q, Cxt Any g Any Any)
  c = dimap unsafeCoerce (\(x, Term y) -> (x, unsafeCoerce y)) -- 🤢🤮🤮

-- | This function runs the given UTT on the given term.

runUpTrans :: (Difunctor f, Difunctor g) => UpTrans f q g -> Term f -> Term g
runUpTrans trans = snd . runUpTransSt trans

-- | This function is a variant of 'runUpTrans' that additionally
-- returns the final state of the run.

runUpTransSt :: (Difunctor f, Difunctor g) => UpTrans f q g -> Term f -> (q, Term g)
runUpTransSt up = cata (upAlg up)

-- | This function generalises 'runUpTrans' to contexts. Therefore,
-- additionally, a transition function for the holes is needed.

runUpTrans' :: forall f g q a b. (Difunctor f, Difunctor g) => UpTrans f q g -> Context f a (q,b) -> (q, Context g a b)
runUpTrans' trans = run where
    run :: Context f a (q,b) -> (q, Context g a b)
    run (Hole (q,b)) = (q, Hole b)
    run (Var a) = (undefined, Var a)
    run (In t) = second appCxt . trans $ dimap id run t

-- | This function composes two UTTs. (see TATA, Theorem 6.4.5)

compUpTrans :: (Difunctor f, Difunctor g, Difunctor h)
               => UpTrans g p h -> UpTrans f q g -> UpTrans f (q,p) h
compUpTrans t2 t1 x = ((q1,q2), c2) where
    (q1, c1) = t1 $ dimap id (\((q1,q2),a) -> (q1,(q2,a))) x
    (q2, c2) = runUpTrans' t2 c1


-- | This function composes a UTT with an algebra.

compAlgUpTrans :: forall f g q a. (Difunctor f, Difunctor g)
               => Alg g a -> UpTrans f q g -> Alg f (q,a)
compAlgUpTrans alg trans = second (cata' alg) . trans . dimap (undefined,) id


-- | This combinator composes a UTT followed by a signature function.

compSigUpTrans :: (Difunctor g) => SigFun g h -> UpTrans f q g -> UpTrans f q h
compSigUpTrans sig trans x = (q, appSigFun sig x') where
    (q, x') = trans x

-- | This combinator composes a signature function followed by a UTT.

compUpTransSig :: UpTrans g q h -> SigFun f g -> UpTrans f q h
compUpTransSig trans sig = trans . sig

-- | This combinator composes a UTT followed by a homomorphism.

compHomUpTrans :: (Difunctor g, Difunctor h) => Hom g h -> UpTrans f q g -> UpTrans f q h
compHomUpTrans hom trans x = (q, appHom hom x') where
    (q, x') = trans x

-- | This combinator composes a homomorphism followed by a UTT.

compUpTransHom :: (Difunctor g, Difunctor h) => UpTrans g q h -> Hom f g -> UpTrans f q h
compUpTransHom trans hom = runUpTrans' trans . hom

-- | This type represents transition functions of total, deterministic
-- bottom-up tree acceptors (UTAs).

type UpState f q = Alg f q

-- | Changes the state space of the UTA using the given isomorphism.

tagUpState :: (Difunctor f) => (q -> p) -> (p -> q) -> UpState f q -> UpState f p
tagUpState i o s = i . s . dimap i o

-- | This combinator runs the given UTA on a term returning the final
-- state of the run.

runUpState :: (Difunctor f) => UpState f q -> Term f -> q
runUpState = cata

-- | This function combines the product UTA of the two given UTAs.

prodUpState :: Difunctor f => UpState f p -> UpState f q -> UpState f (p,q)
prodUpState sp sq t = (p,q) where
    p = sp $ dimap (,undefined) fst t
    q = sq $ dimap (undefined,) snd t


-- | This function constructs a UTT from a given stateful term
-- homomorphism with the state propagated by the given UTA.

upTrans :: forall f g q . (Difunctor f, Difunctor g) => UpState f q -> QHom f q g -> UpTrans f q g
upTrans st f t = (q, c)
    where q = st $ dimap (const undefined) fst t
          c = _ $ cxtMap snd $ explicit f q fst id t

-- | This function applies a given stateful term homomorphism with
-- a state space propagated by the given UTA to a term.

runUpHom :: (Difunctor f, Difunctor g) => UpState f q -> QHom f q g -> Term f -> Term g
runUpHom st hom = snd . runUpHomSt st hom

-- | This is a variant of 'runUpHom' that also returns the final state
-- of the run.

runUpHomSt :: (Difunctor f, Difunctor g) => UpState f q -> QHom f q g -> Term f -> (q,Term g)
runUpHomSt alg h = runUpTransSt (upTrans alg h)


-- | This type represents transition functions of generalised
-- deterministic bottom-up tree acceptors (GUTAs) which have access
-- to the "same" state space.

type DUpState f p q = (q :< p, p :< q) => DUpState' f p q
type DUpState' f p q = forall a b. (?below :: b -> p, ?woleb :: p -> a, ?above :: p) => f a b -> q

-- | This combinator turns an arbitrary UTA into a GUTA.

dUpState :: Difunctor f => UpState f q -> DUpState f p q
dUpState f = f . dimap woleb below

-- | This combinator turns a GUTA with the smallest possible state
-- space into a UTA.

upState :: DUpState f q q -> UpState f q
upState f s = res where res = explicit f res id id s

-- | This combinator runs a GUTA on a term.

runDUpState :: Difunctor f => DUpState f q q -> Term f -> q
runDUpState up = runUpState (upState up)

-- | This combinator constructs the product of two GUTA.  Note that both state spaces must have the same factors.

prodDUpState :: (p :< c, q :< c, c :< p, c :< q)
             => DUpState f c p -> DUpState f c q -> DUpState f c (p,q)
prodDUpState sp sq t = (sp t, sq t)

(|*|) :: (p :< c, q :< c, c :< p, c :< q)
             => DUpState f c p -> DUpState f c q -> DUpState f c (p,q)
(|*|) = prodDUpState


-- | This type represents transition functions of total deterministic
-- top-down tree transducers (DTTs).

type DownTrans f q g = forall a b. q -> f (a -> q) (q -> b) -> Context g a b


-- | This is a variant of the 'DownTrans' type that makes it easier to
-- define DTTs as it avoids the explicit use of 'Hole' to inject
-- placeholders into the result.

type DownTrans' f q g = forall a b. q -> f (Context g a b -> q) (q -> Context g a b) -> Context g a b

-- | This function turns a DTT defined using the type 'DownTrans'' in
-- to the canonical form of type 'DownTrans'.
mkDownTrans :: Difunctor f => DownTrans' f q g -> DownTrans f q g
mkDownTrans tr q t = tr q (dimap (. Var) (Hole .) t)

-- | Thsis function runs the given DTT on the given tree.

runDownTrans :: forall f g q a b h. (Difunctor f, Difunctor g) => DownTrans f q g -> q -> Cxt h f a b -> Cxt h g a b
runDownTrans tr q t = run t q where
    run :: Cxt h f a b -> q -> Cxt h g a b
    run (In t) q = appCxt $ tr q $ dimap _ run t
    run (Hole a) _ = Hole a
    run (Var a) _ = Var a

{-
-- | This function runs the given DTT on the given tree.

runDownTrans' :: (Functor f, Functor g) => DownTrans f q g -> q -> Cxt h f (q -> a) -> Cxt h g a
runDownTrans' tr q t = run t q where
    run (Term t) q = appCxt $ tr q $ fmap run t
    run (Hole a) q = Hole (a q)

-- | This function composes two DTTs. (see W.C. Rounds /Mappings and
-- grammars on trees/, Theorem 2.)

compDownTrans :: (Functor f, Functor g, Functor h)
              => DownTrans g p h -> DownTrans f q g -> DownTrans f (q,p) h
compDownTrans t2 t1 (q,p) t = runDownTrans' t2  p $ t1 q (fmap curry t)



-- | This function composes a signature function after a DTT.

compSigDownTrans :: (Functor g) => SigFun g h -> DownTrans f q g -> DownTrans f q h
compSigDownTrans sig trans q = appSigFun sig . trans q

-- | This function composes a DTT after a function.

compDownTransSig :: DownTrans g q h -> SigFun f g -> DownTrans f q h
compDownTransSig trans hom q t = trans q (hom t)


-- | This function composes a homomorphism after a DTT.

compHomDownTrans :: (Functor g, Functor h)
              => Hom g h -> DownTrans f q g -> DownTrans f q h
compHomDownTrans hom trans q = appHom hom . trans q

-- | This function composes a DTT after a homomorphism.

compDownTransHom :: (Functor g, Functor h)
              => DownTrans g q h -> Hom f g -> DownTrans f q h
compDownTransHom trans hom q t = runDownTrans' trans q (hom t)


-- | This type represents transition functions of total, deterministic
-- top-down tree acceptors (DTAs).

type DownState f q = forall m a. Mapping m a => (q, f a) -> m q


-- | Changes the state space of the DTA using the given isomorphism.

tagDownState :: (q -> p) -> (p -> q) -> DownState f q -> DownState f p
tagDownState i o t (q,s) = fmap i $ t (o q,s)

-- | This function constructs the product DTA of the given two DTAs.

prodDownState :: DownState f p -> DownState f q -> DownState f (p,q)
prodDownState sp sq ((p,q),t) = prodMap p q (sp (p, t)) (sq (q, t))


-- | Apply the given state mapping to the given functorial value by
-- adding the state to the corresponding index if it is in the map and
-- otherwise adding the provided default state.

appMap :: Traversable f => (forall m i . Mapping m i => f i -> m q)
                       -> q -> f (q -> b) -> f (q,b)
appMap qmap q s = fmap qfun s'
    where s' = number s
          qfun (Numbered i a) = let q' = lookupNumMap q i (qmap s')
                                in (q', a q')

-- | This function constructs a DTT from a given stateful term--
-- homomorphism with the state propagated by the given DTA.

downTrans :: (Traversable f, Functor g) => DownState f q -> QHom f q g -> DownTrans f q g
downTrans st f q s = fmap snd $ explicit f q fst (appMap (curry st q) q s)


-- | This function applies a given stateful term homomorphism with a
-- state space propagated by the given DTA to a term.

runDownHom :: (Traversable f, Functor g)
            => DownState f q -> QHom f q g -> q -> Term f -> Term g
runDownHom st h = runDownTrans (downTrans st h)

-- | This type represents transition functions of generalised
-- deterministic top-down tree acceptors (GDTAs) which have access

-- to an extended state space.
type DDownState f p q = (q :< p) => DDownState' f p q

type DDownState' f p q = forall m i . (Mapping m i, ?below :: i -> p, ?above :: p)
                                => f i -> m q

-- | This combinator turns an arbitrary DTA into a GDTA.

dDownState :: DownState f q -> DDownState f p q
dDownState f t = f (above,t)

-- | This combinator turns a GDTA with the smallest possible state
-- space into a DTA.

downState :: DDownState f q q -> DownState f q
downState f (q,s) = res
    where res = explicit f q bel s
          bel k = findWithDefault q k res


-- | This combinator constructs the product of two dependant top-down
-- state transformations.

prodDDownState :: (p :< c, q :< c)
               => DDownState f c p -> DDownState f c q -> DDownState f c (p,q)
prodDDownState sp sq t = prodMap above above (sp t) (sq t)

-- | This is a synonym for 'prodDDownState'.

(>*<) :: (p :< c, q :< c, Functor f)
         => DDownState f c p -> DDownState f c q -> DDownState f c (p,q)
(>*<) = prodDDownState


-- | This combinator combines a bottom-up and a top-down state
-- transformations. Both state transformations can depend mutually
-- recursive on each other.

runDState :: Traversable f => DUpState' f (u,d) u -> DDownState' f (u,d) d -> d -> Term f -> u
runDState up down d (Term t) = u where
        t' = fmap bel $ number t
        bel (Numbered i s) =
            let d' = lookupNumMap d i m
            in Numbered i (runDState up down d' s, d')
        m = explicit down (u,d) unNumbered t'
        u = explicit up (u,d) unNumbered t'

-- | This combinator runs a stateful term homomorphisms with a state
-- space produced both on a bottom-up and a top-down state
-- transformation.

runQHom :: (Traversable f, Functor g) =>
           DUpState' f (u,d) u -> DDownState' f (u,d) d ->
           QHom f (u,d) g ->
           d -> Term f -> (u, Term g)
runQHom up down trans d (Term t) = (u,t'') where
        t' = fmap bel $ number t
        bel (Numbered i s) =
            let d' = lookupNumMap d i m
                (u', s') = runQHom up down trans d' s
            in Numbered i ((u', d'),s')
        m = explicit down (u,d) (fst . unNumbered) t'
        u = explicit up (u,d) (fst . unNumbered) t'
        t'' = appCxt $ fmap (snd . unNumbered) $  explicit trans (u,d) (fst . unNumbered) t'


-- | Lift a stateful term homomorphism over signatures @f@ and @g@ to
-- a stateful term homomorphism over the same signatures, but extended with
-- annotations.
propAnnQ :: (DistAnn f p f', DistAnn g p g', Functor g)
        => QHom f q g -> QHom f' q g'
propAnnQ hom f' = ann p (hom f)
    where (f,p) = projectA f'

-- | Lift a bottom-up tree transducer over signatures @f@ and @g@ to a
-- bottom-up tree transducer over the same signatures, but extended
-- with annotations.
propAnnUp :: (DistAnn f p f', DistAnn g p g', Functor g)
        => UpTrans f q g -> UpTrans f' q g'
propAnnUp trans f' = (q, ann p t)
    where (f,p) = projectA f'
          (q,t) = trans f

-- | Lift a top-down tree transducer over signatures @f@ and @g@ to a
-- top-down tree transducer over the same signatures, but extended
-- with annotations.
propAnnDown :: (DistAnn f p f', DistAnn g p g', Functor g)
        => DownTrans f q g -> DownTrans f' q g'
propAnnDown trans q f' = ann p (trans q f)
    where (f,p) = projectA f'


-- | This function adds unique annotations to a term/context. Each
-- node in the term/context is annotated with its path from the root,
-- which is represented as an integer list. It is implemented as a
-- DTT.
pathAnn :: forall g. (Traversable g) => CxtFun g (g :&: [Int])
pathAnn = runDownTrans trans [] where
    trans :: DownTrans g [Int] (g :&: [Int])
    trans q t = simpCxt (fmap (\ (Numbered n s) -> s (n:q)) (number t) :&: q)
-}
