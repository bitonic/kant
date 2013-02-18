{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Defines instances of 'Pretty' for most types defined.  Exports convenient
--   functions.
module Kant.Pretty (Pretty(..), putPretty) where

import           Data.List (intersperse)
import           Data.String (IsString(..))

import           Text.PrettyPrint.Leijen
                 (Pretty(..), (<+>), (<>), Doc, align, hsep, vcat,
                  (<$>), vsep, group, (<$$>), hcat)
import qualified Text.PrettyPrint.Leijen as PrettyPrint

import           Kant.Term
import           Kant.Sugar
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
    pretty = pretty . (distill :: Term -> STerm)

instance Pretty STerm where
    pretty (SVar v) = pretty v
    pretty (SType 0) = "Type"
    pretty (SType l) = "Type" <> pretty (show l)
    pretty (SArr pars ty) = prettyPars pars " -> " <+> "->" <+> pretty ty
    pretty to@(SApp _ _) = go to
      where
        go (SApp t₁ t₂) = go t₁ <+> singleParens t₂
        go t           = singleParens t
    pretty (SLam pars t) =
        "\\" <> group (nest (prettyPars' pars <> "=>" <$> align (pretty t)))
    pretty (SCase n ty brs) =
        group (nest ("case" <+> pretty n <+> "return" <+> pretty ty <$>
                     (align (prettyBarred prettyBranch brs))))
    pretty (SFix nm pars ty t) =
        "fix" <+> group (nest (prettyFixPars (discardedM nm) pars ty <+> "=>" <$>
                               align (pretty t)))
    pretty SUnknown = "??"

nest :: Doc -> Doc
nest = PrettyPrint.nest 2

singleTerm :: STerm -> Bool
singleTerm (SVar _)  = True
singleTerm (SType _) = True
singleTerm _         = False

singleParens :: STerm -> Doc
singleParens t = if singleTerm t then pt else "(" <> align pt <> ")"
  where pt = pretty t

prettyPars :: [SParam] -> Doc -> Doc
prettyPars pars' d = hcat (intersperse d (go pars'))
  where
    go [] = []
    go ((mns, ty) : pars) =
        (case mns of
             Nothing -> singleParens ty
             Just ns -> "[" <> hsep' ns <+> ":" <+> pretty ty <> "]")
        : go pars

prettyPars' :: [SParam] -> Doc
prettyPars' pars = prettyPars pars " " <> spaceIfCons pars

prettyBarred :: (a -> Doc) -> [a] -> Doc
prettyBarred _ [] = "{ }"
prettyBarred f (x : xs) = vsep ("{" <+> f x : map (("|" <+>) . f) xs ++ ["}"])

prettyBranch :: SBranch -> Doc
prettyBranch (c, ns, t) =
    group (align (pretty c <> spaceIfCons ns <> hsep' ns <+> "=>" <$> pretty t))

typed :: Id -> STerm -> Doc
typed n ty = pretty n <+> ":" <+> pretty ty

instance Pretty SDecl where
    pretty (SVal n pars ty t) =
        group (end (nest (prettyValPars n pars ty <+> "=>" <+>
                          if single then pt else "(" <$$> pt)))
      where
        single = singleTerm t
        pt     = pretty t
        end    = if single then (<> "") else (<$$> ")")
    pretty (SData c pars l cons) =
        group (nest ("data" <+> pretty c <+> prettyPars' pars <> ":" <+>
                     pretty (SType l :: STerm) <$> group (prettyBarred pcon cons)))
      where
        pcon (c', pars') = pretty c' <> spaceIfCons pars' <> align (prettyPars' pars')
    pretty (SPostulate n ty) = "postulate" <+> typed n ty

    prettyList = vcat . intersperse "" . map pretty

prettyFixPars :: Id -> [SParam] -> STerm -> Doc
prettyFixPars n pars ty = pretty n <+> prettyPars' pars <> ":" <+> pretty ty

prettyValPars :: Id -> SValParams -> STerm -> Doc
prettyValPars n (SValParams pars rest) ty =
    pretty n <+> prettyPars' pars <>
    case rest of
        Nothing              -> ""
        Just (pars', pars'') -> "|" <+> prettyPars' pars' <> "|" <+>
                                prettyPars' pars''
    <> ":" <+> pretty ty

instance Pretty SModule where
    pretty = prettyList . unSModule

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
    pretty (NotConstructor c t) =
        group (nest ("Pattern matching on non-constructor '" <> pretty c <>
                     "' in term" <$>
                     pretty t))
    pretty (WrongArity c t) =
        group (nest ("Branch gives wrong number of arguments to constructor `" <>
                     pretty c <> "' in term" <$> pretty t))

instance Pretty Output where
    pretty (OTyCheck ty) = pretty ty
    pretty (OEval t)     = pretty t
    pretty OOK           = "OK"
    pretty OQuit         = "Bye!"
    pretty OSkip         = ""

instance Pretty REPLError where
    pretty (CmdParse err) = group ("Error parsing command:" <$> pretty (show err))
    pretty (TermParse s)  = group ("Error parsing code:" <$> pretty s)
    pretty (TyCheck err)  = group ("Type checking error:" <$> pretty err)
    pretty (IOError err)  = group ("IO error:" <$> pretty (show err))
