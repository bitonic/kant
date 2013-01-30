{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Kant.Pretty (Pretty(..)) where

import           Data.Foldable (Foldable)
import           Data.Maybe (fromMaybe, listToMaybe)

import           Text.PrettyPrint (Doc, text, (<+>), (<>), char, vcat, ($$), hsep)
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

instance Pretty [Char] where
    pretty = text

-- TODO Generalise this for every term
instance Pretty (TermT Id) where
    pretty (Var v)     = pretty v
    pretty (Type 0)    = "Type"
    pretty (Type l)    = "Type" <> text (show l)
    pretty t@(App _ _) = prettyApp t
    pretty (Lam t s)   = "\\" <> pretty n <+> ":" <+> pretty t <+> "=>" <+>
                         pretty t' where (n, t') = freshScope s
    pretty (Case t bs) = "case" <+> pretty t $$
                         nest (prettyBarred prettyBranch bs)

parens :: Term -> Doc
parens t@(Var _)   = pretty t
parens t@(Type _)  = pretty t
parens t           = "(" <> pretty t <> ")"

prettyApp :: Term -> Doc
-- `t₂' should always be equal to `t₃' here
prettyApp (App t₁ (App t₂ (Lam t₃ s))) | t₁ == arrow && t₂ == t₃ =
    case scopeVar s of
        Nothing -> noArr t₂ <+> "->" <+> prettyApp (instantiate1 (Var discarded) s)
        Just n  -> "[" <> pretty n <+> ":" <+> pretty t₂ <> "]" <+> "->" <+>
                   prettyApp (instantiate1 (Var n) s)
  where
    noArr t@(App t' _) | t' /= arrow = pretty t
    noArr t = parens t
prettyApp (App t₁ t₂) = prettyApp t₁ <+> parens t₂
prettyApp t = parens t

prettyBarred :: (a -> Doc) -> [a] -> Doc
prettyBarred _ [] = "{ }"
prettyBarred f (x : xs) = "{" <+> f x $$ vcat (map (("|" <+>) . f) xs) $$ "}"

prettyBranch :: (Id, Int, TScopeT Id Int) -> Doc
prettyBranch (c, i, s) = pretty c <+> hsep (map pretty ns) <+> "=>" <+> pretty t
  where (ns, t) = freshScopeI s i

-- | If the variable is used in a single-variable scope, gets its name
scopeVar :: (Monad f, Foldable f) => Scope (Name n ()) f a -> Maybe n
scopeVar s = listToMaybe [ n | Name n _ <- bindings s ]

freshScope :: TScope Id -> (Id, Term)
freshScope s = (n, instantiate1 (Var n) s) where n = fromMaybe "_" (scopeVar s)

-- TODO this is unsafe, and relies that the 'Int' are all indeed below the bound
-- in the branch body.
freshScopeI :: TScopeT Id Int -> Int -> ([Id], Term)
freshScopeI s i = (vars', instantiateName (map Var vars' !!) s)
  where vars  = [ (ix, n) | Name n ix <- bindings s ]
        vars' = map (\ix -> fromMaybe "_" (lookup ix vars)) [0..(i-1)]

instance Pretty Decl where
    pretty (Val n t)   = pretty n <+> "=" <+> pretty t <> ";"
    pretty (DataDecl d) = pretty d

instance Pretty Data where
    pretty (Data c pars l cons) =
        "data" <+> pretty c <+> prettyPars pars <+> ":" <+>
        pretty (Type l :: Term) $$
        nest (prettyBarred prettyCon cons)

prettyPars :: [Param] -> Doc
prettyPars pars = hsep (map ppar pars)
  where
    ppar (n, t) = if n == discarded then parens t
                  else "[" <> pretty n <+> ":" <+> pretty t <> "]"

prettyCon :: Constr -> Doc
prettyCon (c, pars) = pretty c <+> prettyPars pars

instance Pretty Module where
    pretty (Module decl) = vcat (map pretty decl)