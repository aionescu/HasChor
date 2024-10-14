{-# LANGUAGE AllowAmbiguousTypes, BlockArguments, DataKinds, GADTs, ImpredicativeTypes, PartialTypeSignatures, TypeFamilies #-}
{-# LANGUAGE TypeAbstractions #-}
module Choreography.Location.Multi where

import GHC.TypeLits(KnownSymbol)
import Data.Kind(Constraint)
import Data.Proxy(Proxy(..))
import Data.SOP.BasicFunctors(K(..), mapKK, unK)
import Data.SOP.Classes(HSequence(..), HCollapse(..), hmap, hzipWith)
import Data.SOP.Constraint(All, And, SListI)
import Data.SOP.Dict(Dict(..), withDict, zipAll, mapAll)
import Data.SOP.NP(NP(..), hd, tl)
import GHC.Exts qualified as G(WithDict(..))

import Choreography.Choreo
import Choreography.Location
import Data.SOP.Sing (para_SList, SList (..), sList)

class Member (ls :: [LocTy]) (l :: LocTy) where
  pick :: NP f ls -> f l

type l ∈ ls = Member ls l
type ls ⊆ ls' = All (Member ls') ls

instance {-# OVERLAPPING #-} Member (l : ls) l where
  pick :: NP f (l : ls) -> f l
  pick = hd

instance {-# OVERLAPPABLE #-} Member ls l => Member (l' : ls) l where
  pick :: forall f. NP f (l' : ls) -> f l
  pick = pick . tl

dictMemberHead :: forall l ls. Dict (Member (l : ls)) l
dictMemberHead = Dict -- G.withDict @(Member (l : ls) l) @(forall f. NP f (l : ls) -> f l) hd Dict

dictMemberCons :: forall l' ls l. Dict (Member ls) l -> Dict (Member (l' : ls)) l
dictMemberCons Dict = G.withDict @(Member (l' : ls) l) @(forall f. NP f (l' : ls) -> f l) (pick . tl) Dict

-- TODO: Could probably be implemented in terms of para_SList or cpara_SList
refl :: forall ls. SListI ls => Dict (All (Member ls)) ls
refl =
  case sList @ls of
    SNil -> Dict
    SCons @ls' @l ->
      withDict (dictMemberHead @l @ls') $
        mapAll (dictMemberCons @l @ls') refl `withDict`
          Dict

type a @@ ls = NP ((@) a) ls

-- "pointwise send"
(~>.) :: forall l ls a m. (Applicative m, KnownSymbol l, All KnownSymbol ls, Show a, Read a) => (Proxy l, NP (K a) ls @ l) -> NP Proxy ls -> Choreo m (a @@ ls)
(l, as) ~>. ls =
  zipAll (Dict @(All KnownSymbol) @ls) refl `withDict`
    hctraverse' (Proxy @(KnownSymbol `And` Member ls)) (\(l' :: Proxy l') -> (l, \unwrap -> pure $ unK $ pick @_ @l' $ unwrap as) ~~> l') ls

infix 4 ~>.

-- "scatter"
-- `m` is only used as Applicative here.
-- Could be made parallel by simply instantiating `m` to `Concurrently`?
(~>*) :: (KnownSymbol l, All KnownSymbol ls, Show a, Read a) => (Proxy l, a @ l) -> NP Proxy ls -> Choreo m (a @@ ls)
a ~>* ls = hctraverse' (Proxy @KnownSymbol) (a ~>) ls

infix 4 ~>*

-- "gather"
-- Maybe it's more intuitive to flip the arguments? (*<~)
(*~>) :: forall m l ls a. (Applicative m, KnownSymbol l, All KnownSymbol ls, Show a, Read a) => a @@ ls -> Proxy l -> Choreo m (NP (K a) ls @ l)
as *~> l = unwrapAll l =<< hctraverse' (Proxy @KnownSymbol) (\a -> K <$> ((Proxy, a) ~> l)) as
  where
    unwrapAll :: (Applicative m, KnownSymbol l, All KnownSymbol ls) => Proxy l -> NP (K (a @ l)) ls -> Choreo m (NP (K a) ls @ l)
    unwrapAll l as = locally l \unwrap -> pure $ hmap (mapKK unwrap) as

infix 4 *~>

-- Multiply-located version of `Unwrap`
type Unwraps ls = forall a. a @@ ls -> a

-- The type of a (multi)local computation
type LocalComp m ls a = forall l. (KnownSymbol l, l ∈ ls) => Proxy l -> Unwraps ls -> m a

-- Multiply-located version of `locally`
multilocally :: forall ls a m. All KnownSymbol ls => NP Proxy ls -> LocalComp m ls a -> Choreo m (a @@ ls)
multilocally ls f =
  zipAll (Dict @(All KnownSymbol) @ls) refl `withDict`
    hctraverse' (Proxy @(KnownSymbol `And` Member ls)) (\(l :: Proxy l) -> locally l \unwrap -> f @l Proxy $ unwrap . pick) ls

-- A variant of `~>*` that sends the result of a local computation.
(~~>*) :: (KnownSymbol l, All KnownSymbol ls, Show a, Read a) => (Proxy l, Unwrap l -> m a) -> NP Proxy ls -> Choreo m (a @@ ls)
(~~>*) (l, f) ls = do
  a <- locally l f
  (l, a) ~>* ls

-- A variant of `*~>` that sends the result of a local computation.
(*~~>) :: (Applicative m, KnownSymbol l, All KnownSymbol ls, Show a, Read a) => (NP Proxy ls, LocalComp m ls a) -> Proxy l -> Choreo m (NP (K a) ls @ l)
(*~~>) (ls, f) l = do
  a <- multilocally ls f
  a *~> l
