{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{- |
Module      :  Data.Tuple.Morph
Description :  Morph between tuples with the same "flattened" representation.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  provisional

Allows you to flatten, unflatten and morph tuples of matching types.

Note: by design units are ignored. For example @(Int, (), Char)@ is the same as @(Int, Char)@.
-}
module Data.Tuple.Morph (
    -- * Morphing tuples.
    morph,
    sizeLimit,

    -- * Converting between tuples and HLists.
    Rep,
    HFoldable(..),
    HUnfoldable(..),

    -- * HList parser.
    HParser(..),
    MonoidIndexedMonad(..),
    ) where

import Data.HList.HList (HList(..))
import Data.Proxy
import Data.Type.Equality

import Data.Tuple.Morph.Append
import Data.Tuple.Morph.TH

-- | Recurisvely break down a tuple type, representing it as a type list.
$(mkRep sizeLimit)

-- | Morph a tuple to some isomorphic tuple with the same order of types.
--
-- Works with arbitrary nested tuples, each tuple can have size up to 'sizeLimit'.
--
-- >>> morph ("a", ("b", "c")) :: (String, String, String)
-- ("a","b","c")
--
-- >>> morph ((1 :: Int, 2 :: Int), 3 :: Double) :: (Int, (Int, Double))
-- (1,(2,3.0))
--
-- >>> morph ("a", (), (5 :: Int, (), "c")) :: ((), (String, Int), String)
-- ((),("a",5),"c")
--
-- >>> morph (((("a", "b"), "c"), "d"), "e") :: ((String, String), (String, (String, String)))
-- (("a","b"),("c",("d","e")))
morph :: forall a b. (HFoldable a, HUnfoldable b, Rep a ~ Rep b) => a -> b
morph = case appendRightId (Proxy @(Rep a)) of
    Refl -> fromHList . toHList

-- | Types that can be flattened to a heterogenous list.
class HFoldable t where
    -- | Converts a structure to a heterogenous list.
    toHList :: t -> HList (Rep t)

-- | A function that parses some value @val@ with representation @rep@
-- from a heterogenous list and returns the parsed value and leftovers.
newtype HParser (rep :: [*]) val = HParser {
    -- | Run the parser.
    runHParser :: forall (leftover :: [*]).
                  HList (rep ++ leftover) -> (val, HList leftover)
}

-- | An indexed monad on a monoid.
class MonoidIndexedMonad (m :: k -> * -> *) where
    type Empty :: k
    type Append (x :: k) (y :: k) :: k
    returnMI :: a -> m Empty a
    bindMI :: m x a -> (a -> m y b) -> m (Append x y) b

instance MonoidIndexedMonad HParser where
    type Empty = ('[] :: [*])
    type Append x y = (x ++ y :: [*])

    returnMI a = HParser $ case appendRightId (Proxy :: Proxy leftover) of
      Refl -> \r -> (a, r)

    bindMI :: forall (x :: [*]) a (y :: [*]) b.
              HParser x a -> (a -> HParser y b) -> HParser (Append x y) b
    bindMI m f = HParser $ g
      where
        g :: forall (leftover :: [*]).
             HList ((Append x y) ++ leftover) -> (b, HList leftover)
        g r0 = case appendAssoc (Proxy @x) (Proxy @y) (Proxy @leftover) of
                 Refl -> let (a, r1) = runHParser m r0
                             (b, r2) = runHParser (f a) r1
                         in (b, r2)

-- | Types that can be built from a heterogenous list.
class HUnfoldable t where
    -- | Build a structure from a heterogenous list.
    fromHList :: HList (Rep t) -> t
    fromHList = case appendRightId (Proxy @(Rep t)) of
      Refl -> let parser :: HList (Rep t ++ '[]) -> (t, HList '[])
                  parser = runHParser hListParser
              in fst . parser

    -- | Builds a structure from a heterogenous list and yields the leftovers.
    hListParser :: HParser (Rep t) t

-- HFoldable instances.

instance {-# OVERLAPPING #-} HFoldable () where
    toHList () = HNil

instance {-# OVERLAPPING #-} (Rep a ~ '[a]) => HFoldable a where
    toHList a = HCons a HNil

$(mapM mkHFoldableInst [2 .. sizeLimit])

-- HUnfoldable instances.

instance {-# OVERLAPPING #-} HUnfoldable () where
    hListParser = HParser $ \r -> ((), r)

instance {-# OVERLAPPING #-} (Rep a ~ '[a]) => HUnfoldable a where
    hListParser = HParser $ \(HCons a r) -> (a, r)

$(mapM mkHUnfoldableInst [2 .. sizeLimit])

_test :: (Int, (), ((), Char)) -> (Int, Char)
_test = morph
