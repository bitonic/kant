{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Kant.Pretty (pretty) where

import           Data.Foldable (Foldable)
import           Data.List (groupBy, intersperse)
import           Data.Maybe (fromMaybe, listToMaybe)
import           Data.String (IsString(..))

import           Bound
import           Bound.Name
import           Bound.Scope
import           Text.PrettyPrint.Leijen
                 (Pretty(..), (<+>), (<>), Doc, align, fillSep, hsep, vcat,
                  (<$>), vsep, group, (<$$>))
import qualified Text.PrettyPrint.Leijen as PrettyPrint

import           Kant.Syntax


hsep' :: Pretty a => [a] -> Doc
hsep' = hsep . map pretty

spaceIfCons :: [a] -> Doc
spaceIfCons [] = ""
spaceIfCons _  = " "

instance IsString Doc where
    fromString = pretty

instance a ~ Id => Pretty (TermT a) where
    pretty (Var v) = pretty v
    pretty (Type 0) = "Type"
    pretty (Type l) = "Type" <> pretty (show l)
    pretty to@(App _ _) = go to
      where
        -- 't₂' should always be equal to 't₃' here
        go (App t₁ (App t₂ (Lam t₃ s))) | t₁ == arrow && t₂ == t₃ =
            case scopeVar s of
                Nothing -> noArr t₂ <+> "->" <+> go (instantiate1 (Var discarded) s)
                Just n  -> "[" <> pretty n <+> ":" <+> pretty t₂ <> "]" <+> "->" <+>
                           go (instantiate1 (Var n) s)
          where
            noArr t@(App t' _) | t' /= arrow = pretty t
            noArr t = parens t
        go (App t₁ t₂) = go t₁ <+> parens t₂
        go t = parens t
    pretty to@(Lam tyo _) = "\\" <> group (align (go (tyo, []) to))
      where
        go (ty₁, ns) (Lam ty₂ s) =
            case () of
              _ | n == discarded -> flush <> pretty ty₂ <+> go (ty₂, []) t
              _ | ty₁ == ty₂     -> go (ty₁, n : ns) t
              _ | otherwise      -> flush <> go (ty₂, [n]) t
          where (n, t) = freshScope s
                flush  = prettyPars' (zip (reverse ns) (repeat ty₁))
        go (ty, ns) t = prettyPars' (zip ns (repeat ty)) <> "=>" <$> align (pretty t)
    pretty (Case t₁ brs) =
        group (nest ("case" <+> pretty t₁ <$> (align (prettyBarred pbranch brs))))
      where
        pbranch (c, i, s) = group (align (pretty c <> spaceIfCons ns <>
                                   hsep' ns <+> "=>" <$> pretty t₂))
          where (ns, t₂) = freshScopeI s i

scopeVar :: (Monad f, Foldable f) => Scope (Name n ()) f a -> Maybe n
scopeVar s = listToMaybe [ n | Name n _ <- bindings s ]

freshScope :: TScope Id -> (Id, Term)
freshScope s = (n, instantiate1 (Var n) s)
  where n = fromMaybe discarded (scopeVar s)

-- TODO this is unsafe, and relies that the 'Int' are all indeed below the bound
-- in the branch body.
freshScopeI :: TScopeT Id Int -> Int -> ([Id], Term)
freshScopeI s i = (vars', instantiateList (map Var vars') s)
  where vars  = [ (ix, n) | Name n ix <- bindings s ]
        vars' = [ fromMaybe discarded (lookup ix vars) | ix <- [0..(i-1)] ]

nest :: Doc -> Doc
nest = PrettyPrint.nest 2

parens :: Term -> Doc
parens t@(Var _)   = pretty t
parens t@(Type _)  = pretty t
parens t           = "(" <> align (pretty t) <> ")"

prettyPars :: [Param] -> Doc
prettyPars pars = fillSep (map ppar coll)
  where
    coll = map (\l -> (map fst l, snd (head l))) $
           groupBy (\(n, t) (n', t') ->
                     n /= discarded && n' /= discarded && t == t') pars
    ppar (ns, t) = if ns == [discarded] then parens t
                   else "[" <> hsep' ns <+> ":" <+> pretty t <> "]"

prettyPars' :: [Param] -> Doc
prettyPars' pars = prettyPars pars <> spaceIfCons pars

prettyBarred :: (a -> Doc) -> [a] -> Doc
prettyBarred _ [] = "{ }"
prettyBarred f (x : xs) = vsep ("{" <+> f x : map (("|" <+>) . f) xs ++ ["}"])

instance Pretty Data where
    pretty (Data c pars l cons) =
        group (nest ("data" <+> pretty c <+> prettyPars' pars <> ":" <+>
                     pretty (Type l :: Term) <$> group (prettyBarred pcon cons)))
      where
        pcon (c', pars') = pretty c' <> spaceIfCons pars' <> align (prettyPars' pars')

instance Pretty Decl where
    pretty (Val n t) =
        group (nest (pretty n <+> ":=" <+> pp t) <$$> ")")
      where pp t'@(Var _)  = pretty t'
            pp t'@(Type _) = pretty t'
            pp t'          = "(" <$$> pretty t'
    pretty (Postulate n ty) =
        "postulate" <+> pretty n <+> ":" <+> parens ty
    pretty (DataDecl d) = pretty d

    prettyList = vcat . intersperse "" . map pretty

instance Pretty Module where
    pretty = prettyList . unModule
