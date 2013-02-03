{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Kant.Pretty (pretty) where

import           Data.List (groupBy, intersperse)
import           Data.Maybe (fromMaybe)
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
        go (arrV -> IsArr t₁ Nothing t₂) = noArr t₁ <+> "->" <+> go t₂
        go (arrV -> IsArr t₁ (Just n) t₂) =
            "[" <> pretty n <+> ":" <+> pretty t₁ <> "]" <+> "->" <+> go t₂
        go (App t₁ t₂) = go t₁ <+> singleParens t₂
        go t = singleParens t
        noArr t@(App t' _) | t' /= arrow = pretty t
        noArr t = singleParens t
    pretty to@(Lam tyo _) = "\\" <> group (align (go (tyo, []) to))
      where
        go (ty₁, ns) (Lam ty₂ s) =
            let (n, t) = freshScope s
                flush  = prettyPars' (zip (reverse ns) (repeat ty₁))
            in case () of
                 _ | n == discarded -> flush <> pretty ty₂ <+> go (ty₂, []) t
                 _ | ty₁ == ty₂     -> go (ty₁, n : ns) t
                 _ | otherwise      -> flush <> go (ty₂, [n]) t
        go (ty, ns) t = prettyPars' (zip ns (repeat ty)) <> "=>" <$> align (pretty t)
    pretty (Case t₁ brs) =
        group (nest ("case" <+> pretty t₁ <$> (align (prettyBarred pbranch brs))))
      where
        pbranch (c, i, s) = let (ns, t₂) = freshScopeI s i
                            in group (align (pretty c <> spaceIfCons ns <>
                                             hsep' ns <+> "=>" <$> pretty t₂))

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

singleTerm :: (Doc -> Doc) -> Term -> Doc
singleTerm _ t@(Var _)  = pretty t
singleTerm _ t@(Type _) = pretty t
singleTerm f t          = f (pretty t)

singleParens :: Term -> Doc
singleParens = singleTerm (\d -> "(" <> align d <> ")")

prettyPars :: [Param] -> Doc
prettyPars pars = fillSep (map ppar coll)
  where
    coll = map (\l -> (map fst l, snd (head l))) $
           groupBy (\(n, t) (n', t') ->
                     n /= discarded && n' /= discarded && t == t') pars
    ppar (ns, t) = if ns == [discarded] then singleParens t
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

-- TODO reform the parameters to the values instead of simply having lambdas
instance Pretty Val where
    pretty (Val n ty t) =
        group (nest (pretty n <+> ":" <+> pretty ty <+> ":=" <+>
                     singleTerm ("(" <$$>) t) <$$> ")")

instance Pretty Decl where
    pretty (ValDecl val) = pretty val
    pretty (Postulate n ty) =
        "postulate" <+> pretty n <+> ":" <+> singleParens ty
    pretty (DataDecl d) = pretty d

    prettyList = vcat . intersperse "" . map pretty

instance Pretty Module where
    pretty = prettyList . unModule
