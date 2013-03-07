{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Defines instances of 'Pretty' for most types defined.  Exports convenient
--   functions.
module Kant.Pretty (Pretty(..), putPretty) where

import           Data.String (IsString(..))

import           Text.PrettyPrint.Leijen

import           Kant.Term
import           Kant.Sugar
import           Kant.Distill
import           Kant.TyCheck
import           Kant.REPL.Types

-- | @'putPretty' = 'putStrLn' . 'show' . 'pretty'@.
putPretty :: Pretty a => a -> IO ()
putPretty = putStrLn . show . pretty

instance IsString Doc where
    fromString = pretty

instance (v ~ Id) => Pretty (Term v) where
    pretty = pretty . distill

instance Pretty STerm where
    pretty (SV v) = pretty v
    pretty STy = "*"
    pretty (SArr pars ty) = prettyPis pars <+> pretty ty
    pretty to@(SApp _ _) = go to
      where go (SApp t₁ t₂) = go t₁ <+> singleParens t₂
            go t = singleParens t
    pretty (SLam vs t) =
        "\\" <> hsep (map prettyBs vs) <+> "=>" <+> pretty t
    pretty (SHole hn ts) = "{!" <> pretty hn <+> hsep (map singleParens ts) <> "!}"
    pretty (SAnn pars ty t) =
        "\\" <> hsep (map prettyPar pars) <+> ":" <+> pretty ty <+> "=>" <+> pretty t

nest' :: Doc -> Doc
nest' = nest 2

singleTerm :: STerm -> Bool
singleTerm (SV _)      = True
singleTerm STy         = True
singleTerm (SHole _ _) = True
singleTerm _           = False

singleParens :: STerm -> Doc
singleParens t = if singleTerm t then pt else "(" <> align pt <> ")"
  where pt = pretty t

-- TODO Group equal types in `prettyPis' and `prettyPar'

prettyPis :: [SParam] -> Doc
prettyPis pars' = hsep (go pars')
  where
    go [] = []
    go ((mns, ty) : pars) =
        (case mns of
             Nothing -> mapp ty <+> "->"
             Just ns -> "[" <> pretty ns <+> ":" <+> pretty ty <> "]" <+>
                        marr pars)
        : go pars
    marr ((Just _, _) : _)  = ""
    marr _                  = "->"
    mapp t@(SApp _ _) = pretty t
    mapp t            = singleParens t

prettyPar :: SParam -> Doc
prettyPar (mn, ty) = "[" <> n <+> ":" <+> pretty ty <> "]"
  where n = case mn of
                Nothing -> "_"
                Just n' -> pretty n'

prettyBs :: Maybe Id -> Doc
prettyBs Nothing  = "_"
prettyBs (Just n) = pretty n

instance Pretty HoleCtx where
    pretty HoleCtx{holeName = hn, holeGoal = goal, holeCtx = hctx} =
        nest' (rest ("Hole" <+> pretty hn <+> ":" <+> pretty goal))
      where
        rest = if null hctx then id
               else (<$$> vcat [pretty t <+> ":" <+> pretty ty | (t, ty) <- hctx])

    prettyList = vcat . map pretty

instance Pretty TyCheckError where
    pretty TyCheckError = "fixme"
    pretty (OutOfBounds n) = "Out of bound variable `" <> pretty n <> "'"
    pretty (DuplicateName n) = "Duplicate name `" <> pretty n <> "'"
    pretty (Mismatch ty₁ t ty₂) =
        group (nest' ("Expecting type" <$> pretty ty₁) <$>
               nest' ("for term" <$> pretty t) <$>
               nest' ("instead of" <$> pretty ty₂))
    pretty (ExpectingFunction t ty) =
        group (nest' ("Expecting function type for term" <$> pretty t) <$>
               nest' ("instead of" <$> pretty ty))
    pretty (ExpectingType t ty) =
        group (nest' ("Expecting a Type for term" <$> pretty t) <$>
               nest' ("instead of" <$> pretty ty))
    pretty (ExpectingTypeCon tyc ty) =
        group (nest' ("Expecting Type as return type for type constructor" <+>
                      pretty tyc <+> "instead of" <$> pretty ty))
    pretty (ExpectingTypeData dc tyc ty) =
        group (nest' ("Expecting something constructing a" <+> pretty tyc <+>
                      "for data constructor" <+> pretty dc <+> "instead of" <$>
                      pretty ty))
    pretty (WrongRecTypePos dc tyc ty) =
        group (nest' ("Recursive occurrence of" <+> pretty tyc <+>
                      "in wrong position in data constructor" <+> pretty dc <+>
                      "of type" <$> pretty ty))
    pretty (UntypedTerm ty) =
        group (nest' ("Type can't be inferred for term" <+> pretty ty))
    pretty (UnexpectedHole hn) = "Unexpected hole `" <> pretty hn <> "'."

instance Pretty Output where
    pretty (OTyCheck ty [])    = pretty ty
    pretty (OTyCheck ty holes) = prettyList holes <$$> pretty ty
    pretty (OPretty t)         = pretty t
    pretty (OHoles [])         = "OK"
    pretty (OHoles holes)      = prettyList holes
    pretty OOK                 = "OK"
    pretty OQuit               = "Bye!"
    pretty OSkip               = ""

instance Pretty REPLError where
    pretty (CmdParse err) = group ("Error parsing command:" <$> pretty (show err))
    pretty (TermParse s)  = group ("Error parsing code:" <$> pretty s)
    pretty (TyCheck err)  = group ("Type checking error:" <$> pretty err)
    pretty (IOError err)  = group ("IO error:" <$> pretty (show err))
