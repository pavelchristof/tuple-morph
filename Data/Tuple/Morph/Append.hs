{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{- |
Module      :  Data.Tuple.Morph.Append
Description :  Appending type lists.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

Appending type lists and HLists.
-}
module Data.Tuple.Morph.Append where

import Data.HList.HList (HList(..))
import Data.Proxy
import Data.Type.Equality
import Unsafe.Coerce

infixr 5 ++, ++@

-- | Appends two type lists.
type family (++) (a :: [k]) (b :: [k]) :: [k] where
    '[]       ++ b = b
    (a ': as) ++ b = a ': (as ++ b)

-- TODO: Proofs could use some love when GHC 7.10 comes out.

-- | Proof (by unsafeCoerce) that appending is associative.
appendAssoc :: Proxy a -> Proxy b -> Proxy c
            -> ((a ++ b) ++ c) :~: (a ++ (b ++ c))
appendAssoc _ _ _ = unsafeCoerce Refl

-- | Proof (by unsafeCoerce) that '[] is a right identity of (++).
appendRightId :: Proxy a -> (a ++ '[]) :~: a
appendRightId _ = unsafeCoerce Refl

class Appendable as bs where
  (++@) :: HList as -> HList bs -> HList (as ++ bs)

instance Appendable '[] bs where
  HNil ++@ bs = bs

instance Appendable as bs => Appendable (a ': as) bs where
  HCons a as ++@ bs = HCons a (as ++@ bs)
