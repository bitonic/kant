{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Kant.Pretty (Pretty(..)) where

import           Data.Foldable (Foldable)
import           Data.Maybe (fromMaybe, listToMaybe)

import           Text.PrettyPrint (Doc, text, (<+>), (<>), char, hcat, vcat, ($$))
import qualified Text.PrettyPrint as PrettyPrint

import           Kant.Syntax

import           Bound
import           Bound.Name
import           Bound.Scope

nest :: Doc -> Doc
nest = PrettyPrint.nest 4

class Pretty a where
    pretty :: a -> Doc

instance Pretty Char where
    pretty = char

instance Pretty a => Pretty [a] where
    pretty = hcat . map pretty

-- TODO Generalise this for every term
instance Pretty (TermT Id) where
    pretty (Var v)     = pretty v
    pretty (Type l)    = "Type" <> text (show l)
    pretty t@(App _ _) = prettyApp t
    pretty (Lam t s)   = "\\" <> pretty v <+> ":" <+> pretty t <+> "->" <+>
                         pretty t' where (v, t') = freshScope s
    pretty (Case t bs) = "case" <+> pretty t $$
                         nest (vcat (map prettyBranch bs)) $$
                         "end"

parens :: Term -> Doc
parens t@(Var _)   = pretty t
parens t@(Type _)  = pretty t
parens t           = "(" <> pretty t <> ")"

prettyApp :: Term -> Doc
prettyApp (App t m) = prettyApp t <+> parens m
prettyApp t         = parens t

prettyBranch :: (Id, Int, TScopeT Id Int) -> Doc
prettyBranch (c, i, s) =
    "|" <+> pretty c <+> hcat (map pretty vs) <+> "->" <+> pretty t
  where (vs, t) = freshScopeI s i

-- | If the variable is used in a single-variable scope, gets its name
scopeVar :: (Monad f, Foldable f) => Scope (Name n ()) f a -> Maybe n
scopeVar s = listToMaybe [ n | Name n _ <- bindings s ]

freshScope :: TScope Id -> (Id, Term)
freshScope s = (v, instantiate1 (Var v) s) where v = fromMaybe "" (scopeVar s)

-- TODO this is unsafe, and relies that the 'Int' are all indeed below the bound
-- in the branch body.
freshScopeI :: TScopeT Id Int -> Int -> ([Id], Term)
freshScopeI s n = (vars', instantiateName (map Var vars' !!) s)
  where vars  = [ (i, n') | Name n' i <- bindings s ]
        vars' = map (\i -> fromMaybe "_" (lookup i vars)) [0..(n-1)]
