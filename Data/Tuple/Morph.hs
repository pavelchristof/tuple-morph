{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{- |
Module      :  Data.Tuple.Morph
Description :  Morph isomorphic tuples.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

Allows you to flatten, unflatten and morph tuples of matching types.
-}
module Data.Tuple.Morph (
    morph,
    Rep,
    HFoldable(..),
    HUnfoldable(..),
    HParser(..)
    ) where

import Data.HList.HList (HList(..))
import Data.Proxy
import Data.Type.Equality
import Unsafe.Coerce

-- | Morph a tuple to some isomorphic tuple.
morph :: forall a b. (HFoldable a, HUnfoldable b, Rep a ~ Rep b) => a -> b
morph = case appendRightId (Proxy :: Proxy (Rep a)) of
    Refl -> fromHList . toHList

-- | Recurisvely break down a tuple, representing it as a type list.
type family Rep (a :: *) :: [*] where
    Rep (a, b, c, d, e) = Rep a ++ Rep b ++ Rep c ++ Rep d ++ Rep e
    Rep (a, b, c, d) = Rep a ++ Rep b ++ Rep c ++ Rep d
    Rep (a, b, c) = Rep a ++ Rep b ++ Rep c
    Rep (a, b) = Rep a ++ Rep b
    Rep () = '[]
    Rep a = '[a]

-- | Types that can be flattened to a heterogenous list.
class HFoldable t where
    -- | Converts a structure to a heterogenous list.
    toHList :: t -> HList (Rep t)

-- | A function that parses some value @val@ with representation @rep@
-- from a heterogenous list and returns the parsed value and leftover.
newtype HParser rep val = HParser {
    -- | Run the parser.
    runHParser :: forall (leftover :: [*]). 
                 HList (rep ++ leftover) -> (val, HList leftover) 
}

-- | Types that can be built from a heterogenous list.
class HUnfoldable t where
    -- | Build a structure from a heterogenous list.
    fromHList :: HList (Rep t) -> t
    fromHList = case appendRightId (Proxy :: Proxy (Rep t)) of 
      Refl -> let parser :: HList (Rep t ++ '[]) -> (t, HList '[])
                  parser = runHParser hListParser
              in fst . parser

    -- | Builds a structure from a heterogenous list and yields the leftovers.
    hListParser :: HParser (Rep t) t


type family (++) (a :: [*]) (b :: [*]) :: [*] where
    '[]       ++ b = b
    (a ': as) ++ b = a ': (as ++ b)

appendAssoc :: Proxy a -> Proxy b -> Proxy c 
            -> ((a ++ b) ++ c) :~: (a ++ (b ++ c))
appendAssoc _ _ _ = unsafeCoerce Refl

appendRightId :: Proxy a -> (a ++ '[]) :~: a
appendRightId _ = unsafeCoerce Refl

(++@) :: HList a -> HList b -> HList (a ++ b)
HNil         ++@ ys = ys
(HCons x xs) ++@ ys = HCons x (xs ++@ ys)



instance (HFoldable a, HFoldable b, HFoldable c, HFoldable d, HFoldable e) => HFoldable (a, b, c, d, e) where
    toHList (a, b, c, d, e) = toHList a ++@ toHList b ++@ toHList c ++@ toHList d ++@ toHList e

instance (HFoldable a, HFoldable b, HFoldable c, HFoldable d) => HFoldable (a, b, c, d) where
    toHList (a, b, c, d) = toHList a ++@ toHList b ++@ toHList c ++@ toHList d

instance (HFoldable a, HFoldable b, HFoldable c) => HFoldable (a, b, c) where
    toHList (a, b, c) = toHList a ++@ toHList b ++@ toHList c

instance (HFoldable a, HFoldable b) => HFoldable (a, b) where
    toHList (a, b) = toHList a ++@ toHList b

instance HFoldable () where
    toHList () = HNil

instance (Rep a ~ '[a]) => HFoldable a where
    toHList a = HCons a HNil

returnWTF :: a -> HParser '[] a
returnWTF a = HParser $ \r -> (a, r)

(>>>=) :: forall (a :: *) (aRep :: [*]) (b :: *) (bRep :: [*]).
          HParser aRep a -> (a -> HParser bRep b) -> HParser (aRep ++ bRep) b
m >>>= f = HParser g
  where
    g :: forall (leftover :: [*]). 
         HList (aRep ++ bRep ++ leftover) -> (b, HList leftover)
    g r0 = case appendAssoc (Proxy :: Proxy aRep) 
                            (Proxy :: Proxy bRep)
                            (Proxy :: Proxy leftover) of
              Refl -> let (a, r1) = runHParser m r0
                          (b, r2) = runHParser (f a) r1
                      in (b, r2)

instance (HUnfoldable a, HUnfoldable b, HUnfoldable c, HUnfoldable d) => HUnfoldable (a, b, c, d) where
    hListParser = case appendRightId (Proxy :: Proxy (Rep d)) of
                  Refl -> hListParser >>>= (\(a, b, c) ->
                          hListParser >>>= (\d ->
                          returnWTF (a, b, c, d)))

instance (HUnfoldable a, HUnfoldable b, HUnfoldable c) => HUnfoldable (a, b, c) where
    hListParser = case appendRightId (Proxy :: Proxy (Rep c)) of
                  Refl -> hListParser >>>= (\(a, b) ->
                          hListParser >>>= (\c ->
                          returnWTF (a, b, c)))

instance (HUnfoldable a, HUnfoldable b) => HUnfoldable (a, b) where
    hListParser = case appendRightId (Proxy :: Proxy (Rep b)) of 
                  Refl -> hListParser >>>= (\a ->
                          hListParser >>>= (\b ->
                          returnWTF (a, b)))

instance (Rep a ~ '[a]) => HUnfoldable a where
    hListParser = HParser $ \(HCons a r) -> (a, r)

instance HUnfoldable () where
    hListParser = HParser $ \r -> ((), r)



