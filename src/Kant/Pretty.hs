{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Defines instances of 'Pretty' for most types defined.  Exports convenient
--   functions.
module Kant.Pretty (Pretty(..), putPretty) where

import           Data.List (intersperse)
import           Data.String (IsString(..))

import           Text.PrettyPrint.Leijen
                 (Pretty(..), (<+>), (<>), Doc, align, hsep, vcat, (<$>), vsep,
                  group, (<$$>), hcat)
import qualified Text.PrettyPrint.Leijen as PrettyPrint

import           Kant.Term
import           Kant.Sugar
import           Kant.Distill
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

instance (v ~ Id) => Pretty (Term v) where
    pretty = pretty . distill

instance Pretty STerm where
    pretty (SV v) = pretty v
    pretty STy = "Type"
    pretty (SArr pars ty) = prettyPars pars <+> "->" <+> pretty ty
    pretty to@(SApp _ _) = go to
      where
        go (SApp t₁ t₂) = go t₁ <+> singleParens t₂
        go t           = singleParens t
    pretty (SLam pars t) =
        "\\" <> group (nest (prettyPars' pars <> "=>" <$> align (pretty t)))

nest :: Doc -> Doc
nest = PrettyPrint.nest 2

singleTerm :: STerm -> Bool
singleTerm (SV _)  = True
singleTerm STy = True
singleTerm _       = False

singleParens :: STerm -> Doc
singleParens t = if singleTerm t then pt else "(" <> align pt <> ")"
  where pt = pretty t

prettyPars :: [SParam] -> Doc
prettyPars pars' = hcat (intersperse " " (go pars'))
  where
    go [] = []
    go ((mns, ty) : pars) =
        (case mns of
             Nothing -> singleParens ty
             Just ns -> "[" <> hsep' ns <+> ":" <+> align (pretty ty) <> "]")
        : go pars

prettyPars' :: [SParam] -> Doc
prettyPars' pars = prettyPars pars <> spaceIfCons pars

prettyBarred :: (a -> Doc) -> [a] -> Doc
prettyBarred _ [] = "{ }"
prettyBarred f (x : xs) = vsep ("{" <+> f x : map (("|" <+>) . f) xs ++ ["}"])

typed :: Id -> STerm -> Doc
typed n ty = pretty n <+> ":" <+> pretty ty

instance Pretty SDecl where
    pretty (SVal n pars t) =
        group (end (nest (pretty n <+> prettyPars' pars <> "=>" <+>
                          if single then pt else "(" <$$> pt)))
      where
        single = singleTerm t
        pt     = pretty t
        end    = if single then (<> "") else (<$$> ")")
    pretty (SData c pars cons) =
        group (nest ("data" <+> pretty c <+> prettyPars' pars <+>
                     group (prettyBarred (uncurry typed) cons)))
    pretty (SPostulate n ty) = "postulate" <+> typed n ty

    prettyList = vcat . intersperse "" . map pretty
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
    pretty (ExpectingTypeCon tyc ty) =
        group (nest ("Expecting Type as return type for type constructor" <+>
                     pretty tyc <+> "instead of" <$> pretty ty))
    pretty (ExpectingTypeData dc tyc ty) =
        group (nest ("Expecting something constructing a" <+> pretty tyc <+>
                     "for data constructor" <+> pretty dc <+> "instead of" <$>
                     pretty ty))
    pretty (WrongRecTypePos dc tyc ty) =
        group (nest ("Recursive occurrence of" <+> pretty tyc <+>
                     "in wrong position in data constructor" <+> pretty dc <+>
                     "of type" <$> pretty ty))

instance Pretty Output where
    pretty (OTyCheck ty) = pretty ty
    pretty (OPretty t)   = pretty t
    pretty OOK           = "OK"
    pretty OQuit         = "Bye!"
    pretty OSkip         = ""

instance Pretty REPLError where
    pretty (CmdParse err) = group ("Error parsing command:" <$> pretty (show err))
    pretty (TermParse s)  = group ("Error parsing code:" <$> pretty s)
    pretty (TyCheck err)  = group ("Type checking error:" <$> pretty err)
    pretty (IOError err)  = group ("IO error:" <$> pretty (show err))
