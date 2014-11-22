{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{- |
Module      :  Data.Tuple.Morph.TH
Description :  Template haskell used to generate instances.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental
-}
module Data.Tuple.Morph.TH where

import Data.Tuple.Morph.Append
import Language.Haskell.TH

-- | Creates the "Rep" type family.
mkRep :: Int -> Q [Dec]
mkRep n = fmap (:[])
        $ closedTypeFamilyKindD (mkName "Rep")
              [(PlainTV (mkName "tuple"))] (AppT ListT StarT)
        -- Try to match tuples from biggest to smallest.
        $ map mkEqn [n, n-1 .. 2] ++ map return
        -- Match the unit after all tuples but before the base case.
        [ TySynEqn [TupleT 0] PromotedNilT
        , TySynEqn [a] (AppT (AppT PromotedConsT a) PromotedNilT)
        ]
  where
    a = VarT (mkName "a")
    repName = mkName "Rep"
    append = VarT ''(++)
    mkEqn k = do
        names <- sequence $ take k $ map (newName . (:[])) ['a' .. 'z']
        let -- a, b, c, ...
            vars = map VarT names
            -- (a, b, c, ...)
            tuple = foldl AppT (TupleT k) vars
            -- Rep a, Rep b, Rep c, ...
            reps = map (AppT (ConT repName)) vars
            -- Rep a ++ Rep b ++ Rep c ++ ...
            rep = foldl1 (\x y -> AppT (AppT append x) y) reps
        return $ TySynEqn [tuple] rep
