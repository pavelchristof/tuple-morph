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
module Data.Tuple.Morph.TH (
    sizeLimit,
    mkRep,
    mkHFoldableInst
    ) where

import Control.Monad
import Data.Tuple.Morph.Append
import Language.Haskell.TH

-- | Generates names starting with letters of the alphabet, then
-- pairs of letters, triples of letters and so on.
mkNames :: Int -> [Name]
mkNames n = take n $ map mkName $ [1 ..] >>= flip replicateM ['a' .. 'z']

tupleFrom :: [Type] -> Type
tupleFrom vars = foldl AppT (TupleT (length vars)) vars

-- | Size of the largest tuple that this library will work with. Equal to 13.
--
-- Note that size of ((((((1, 1), 1), 1), 1), 1), 1) is 2, not 7.
sizeLimit :: Int
sizeLimit = 13

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
        let names = mkNames k
            -- a, b, c, ...
            vars = map VarT names
            -- (a, b, c, ...)
            tuple = tupleFrom vars
            -- Rep a, Rep b, Rep c, ...
            reps = map (AppT (ConT repName)) vars
            -- Rep a ++ Rep b ++ Rep c ++ ...
            rep = foldr1 (\x y -> AppT (AppT append x) y) reps
        return $ TySynEqn [tuple] rep

-- | Creates a HFoldable instance for @k@ element tuples.
mkHFoldableInst :: Name -> Int -> Q Dec
mkHFoldableInst className k = do
    let names = mkNames k
        -- types a, b, c, ...
        vars = map VarT names
        -- type (a, b, c, ...)
        tuple = tupleFrom vars
        -- pattern (a, b, c, ...)
        tupleP = TupP $ map VarP names
        toHListName = mkName "toHList"
        -- toHList a, toHList b, toHList c, ...
        hlists = map (\n -> AppE (VarE toHListName) (VarE n)) names
        -- toHList a ++@ toHList b ++@ toHList c ++@ ...
        body = NormalB $ foldr1 (\x y -> AppE (AppE (VarE '(++@)) x) y) hlists
        toHList = FunD toHListName [Clause [tupleP] body []]
    return $ InstanceD
             [ClassP className [var] | var <- vars]
             (AppT (ConT className) tuple)
             [toHList]
