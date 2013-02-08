{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Defines instances of 'Pretty' for most types defined.  Exports convenient
--   functions.
module Kant.Pretty (Pretty(..), putPretty) where

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
import           Kant.TyCheck
import           Kant.REPL.Types


-- | @'putPretty' = 'putStrLn' . 'show' . 'pretty'@.
putPretty :: Pretty a => a -> IO ()
putPretty = putStrLn . show . pretty

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
        go (arrV id -> IsArr t s) =
            case scopeVar s of
                Nothing -> noArr t <+> "->" <+>
                           go (instantiate1 (Var discarded) s)
                Just n  -> "(" <> typed n t <> ")" <+> "->" <+>
                           go (instantiate1 (Var n) s)
        go (App t₁ t₂) = go t₁ <+> singleParens t₂
        go t = singleParens t
        -- Note that we don't need to consider lambdas here since lambdas are
        -- values and we don't even parse arrow types with lambdas, see 'Arr'
        -- rule in Parser.y
        noArr t@(arrV id -> IsArr _ _) = singleParens t
        noArr t                        = pretty t
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
    pretty (Case t₁ ty brs) =
        group (nest ("case" <+> pretty t₁ <+> "return" <+> pretty ty <$>
                     (align (prettyBarred prettyBranch brs))))

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

prettyBranch :: Branch -> Doc
prettyBranch (c, i, s) =
    group (align (pretty c <> spaceIfCons ns <> hsep' ns <+> "=>" <$> pretty t₂))
  where (ns, t₂) = freshScopeI s i

typed :: Id -> Term -> Doc
typed n ty = pretty n <+> ":" <+> pretty ty

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
    pretty (ValDecl val)    = pretty val
    pretty (Postulate n ty) = "postulate" <+> typed n ty
    pretty (DataDecl d)     = pretty d

    prettyList = vcat . intersperse "" . map pretty

instance Pretty Module where
    pretty = prettyList . unModule

instance Pretty TyCheckError where
    pretty TyCheckError = "fixme"
    pretty (OutOfBounds n) = "Out of bound variable `" <> pretty n <> "'"
    pretty (DuplicateName n) = "Duplicate name `" <> pretty n <> "'"
    pretty (Mismatch ty₁ t ty₂) =
        group (nest ("Expecting type" <$> pretty ty₁) <$>
               nest ("for term" <$> pretty t) <$>
               nest ("instead of" <$> pretty ty₂))
    pretty (ExpectingFunction t ty) =
        group (nest ("Expecting function type for term" <$> pretty t) <$>
               nest ("instead of" <$> pretty ty))
    pretty (ExpectingType t ty) =
        group (nest ("Expecting a Type for term" <$> pretty t) <$>
               nest ("instead of" <$> pretty ty))
    pretty (ExpectingCanonical t ty) =
        group (nest ("Expecting canonical (non-arrow) type for term" <$>
                     pretty t) <$>
               nest ("instead of" <$> pretty ty))
    pretty (WrongBranchNumber t) =
        group (nest ("Too few or too many branches in term" <$> pretty t))
    pretty (NotConstructor br) =
        group (nest ("Pattern matching on a non-constructor in branch" <$>
                     prettyBranch br))
    pretty (WrongArity br) =
        group (nest ("Branch gives wrong number of arguments to constructor" <$>
                     prettyBranch br))

instance Pretty Output where
    pretty (OTyCheck ty) = pretty ty
    pretty (OEval t)     = pretty t
    pretty ODecl         = "OK"
    pretty OQuit         = "Bye!"
    pretty OSkip         = ""

instance Pretty Error where
    pretty (CmdParse err) = group ("Error parsing command:" <$> pretty (show err))
    pretty (TermParse s)  = group ("Error parsing code:" <$> pretty s)
    pretty (TyCheck err)  = group ("Type checking error:" <$> pretty err)
