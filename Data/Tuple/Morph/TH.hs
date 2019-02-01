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
    mkHFoldableInst,
    mkHUnfoldableInst
    ) where

import Control.Monad
import Data.Proxy
import Data.Tuple.Morph.Append
import Data.Type.Equality
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
        $ closedTypeFamilyD (mkName "Rep")
              [(PlainTV (mkName "tuple"))] (KindSig (AppT ListT StarT))
              Nothing
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

mkInst :: Name -> Int -> ([Name] -> [Dec]) -> Dec
mkInst className k decs =
    let names = mkNames k
        tvars = map VarT names
        rep = ConT $ mkName "Rep"
        tvars' = AppT rep <$> tvars

        -- Add an Appendable instance to the context for every append we do
        (appendables, _) = foldr
          (\a (instances, tailTy) ->
            ( ConT ''Appendable `AppT` a `AppT` tailTy : instances
            , ConT ''(++) `AppT` a `AppT` tailTy
            ))
          ([], last tvars')
          (init tvars')

    in InstanceD (Just Overlapping)
                 ([AppT (ConT className) tvar | tvar <- tvars] ++ appendables)
                 (AppT (ConT className) (tupleFrom tvars))
                 (decs names)

-- | Creates a HFoldable instance for @k@ element tuples.
mkHFoldableInst :: Int -> Q Dec
mkHFoldableInst k = return $ mkInst (mkName "HFoldable") k $ \names ->
    let toHListName = mkName "toHList"
        -- pattern (a, b, c, ...)
        tupleP = TupP $ map VarP names
        -- toHList a, toHList b, toHList c, ...
        hlists = map (\n -> AppE (VarE toHListName) (VarE n)) names
        -- toHList a ++@ toHList b ++@ toHList c ++@ ...
        body = NormalB $ foldr1 (\x y -> AppE (AppE (VarE '(++@)) x) y) hlists
        toHList = FunD toHListName [Clause [tupleP] body []]
    in [toHList]

-- | Creates a HUnfoldable instance for @k@ element tuples.
mkHUnfoldableInst :: Int -> Q Dec
mkHUnfoldableInst k = return $ mkInst (mkName "HUnfoldable") k $ \names ->
    let hListParserName = mkName "hListParser"
        repName = mkName "Rep"
        bindMIName = mkName "bindMI"
        returnMIName = mkName "returnMI"

        -- Proxy :: Proxy (Rep z)
        proxy = SigE (ConE 'Proxy)
                     (AppT (ConT ''Proxy)
                           (AppT (ConT repName)
                                 (VarT $ last names)))

        -- appendRightId proxy
        theorem = AppE (VarE 'appendRightId) proxy

        -- bindMI hListParser (\a ->
        -- bindMI hListParser (\b ->
        -- ...
        -- returnMI (a, b, c, ...))...)
        bindE n e = AppE (AppE (VarE bindMIName)
                               (VarE hListParserName))
                         (LamE [VarP n] e)
        returnE = (AppE (VarE returnMIName) (TupE (map VarE names)))

        matchBody = NormalB $ foldr bindE returnE names

        -- case theorem of Refl -> ???
        body = NormalB $ CaseE theorem [Match (ConP 'Refl []) matchBody []]
        hListParser = FunD hListParserName [Clause [] body []]
    in [hListParser]
