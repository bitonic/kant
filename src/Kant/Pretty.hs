{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Defines instances of 'Pretty' for most types defined.  Exports convenient
--   functions.
module Kant.Pretty (Pretty(..), putPretty) where

import           Data.String (IsString(..))

import           Text.PrettyPrint.Leijen

import           Kant.Distill
import           Kant.Error
import           Kant.Monad
import           Kant.REPL.Types
import           Kant.Sugar
import           Kant.Term

-- | @'putPretty' = 'putStrLn' . 'show' . 'pretty'@.
putPretty :: Pretty a => a -> IO ()
putPretty = putStrLn . show . pretty

instance IsString Doc where
    fromString = pretty

instance (v ~ Id) => Pretty (Tm r v) where
    pretty = pretty . distill

instance Pretty (STm r) where
    pretty (SV v) = pretty v
    pretty (STy _) = "*"
    pretty (SArr pars ty) = prettyPis pars <+> pretty ty
    pretty to@(SApp _ _) = go to
      where go (SApp t₁ t₂) = go t₁ <+> singleParens t₂
            go t = singleParens t
    pretty (SLam vs t) =
        "\\" <> hsep (map prettyBs vs) <+> "=>" <+> pretty t
    pretty (SHole hn ts) = "{!" <> pretty hn <+> hsep (map singleParens ts) <> "!}"
    pretty (SAnn pars ty t) =
        "\\" <> hsep (map prettyPar pars) <+> ":" <+> pretty ty <+> "=>" <+> pretty t
    pretty (SPrim n) = "$" <> pretty n

nest' :: Doc -> Doc
nest' = nest 2

gnest :: Doc -> Doc
gnest = group . nest'

singleTm :: STm r -> Bool
singleTm (SV _)      = True
singleTm (STy _)     = True
singleTm (SHole _ _) = True
singleTm (SPrim _)   = True
singleTm _           = False

singleParens :: STm r -> Doc
singleParens t = if singleTm t then pt else "(" <> align pt <> ")"
  where pt = pretty t

-- TODO Group equal types in `prettyPis' and `prettyPar'

prettyPis :: [SParam r] -> Doc
prettyPis pars' = hsep (go pars')
  where
    go []                       = []
    go ((Nothing, ty)   : pars) = (mapp ty <+> "->") : go pars
    go (par@(Just _, _) : pars) = marr pars (prettyPar par) : go pars
    marr ((Just _, _) : _)  = id
    marr _                  = (<+> "->")
    mapp t@(SApp _ _) = pretty t
    mapp t            = singleParens t

prettyPar :: SParam r -> Doc
prettyPar (mn, ty) = "[" <> n <+> ":" <+> pretty ty <> "]"
  where n = case mn of
                Nothing -> "_"
                Just n' -> pretty n'

prettyBs :: Maybe Id -> Doc
prettyBs Nothing  = "_"
prettyBs (Just n) = pretty n

instance Pretty HoleCtx where
    pretty HoleCtx{holeName = hn, holeGoal = goal, holeCtx = hctx} =
        nest' (rest (pretty hn <+> ":" <+> pretty goal))
      where
        rest = if null hctx then id
               else (<$$> vcat [pretty t <+> ":" <+> pretty ty | (t, ty) <- hctx])

    prettyList = vcat . map pretty

instance Pretty KError where
    pretty (OutOfBounds n) = "Out of bound variable `" <> pretty n <> "'"
    pretty (DuplicateName n) = "Duplicate name `" <> pretty n <> "'"
    pretty (Mismatch ty₁ t ty₂) =
        group (nest' ("Expecting type" <$> pretty ty₁) <$>
               nest' ("for term" <$> pretty (show t)) <$>
               nest' ("instead of" <$> pretty ty₂))
    pretty (ExpectingFunction (Just t) ty) =
        group (nest' ("Expecting function type for term" <$> pretty t) <$>
               nest' ("instead of" <$> pretty ty))
    pretty (ExpectingFunction Nothing ty) =
        group (nest' ("Expecting function type instead of" <$> pretty ty))
    pretty (ExpectingType t ty) =
        group (nest' ("Expecting a * for term" <$> pretty t) <$>
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
    pretty (UntypedTm ty) =
        group (nest' ("Type can't be inferred for term" <+> pretty ty))
    pretty (UnexpectedHole hn) = "Unexpected hole `" <> pretty hn <> "'."
    pretty CyclicTypes = "Cyclic types."
    pretty (CmdParse err) = gnest ("Error parsing command:" <$> pretty (show err))
    pretty (TmParse s)  = gnest ("Error parsing code:" <$> pretty s)
    pretty (IOError err)  = gnest ("IO error:" <$> pretty (show err))

instance Pretty Output where
    pretty (OTyCheck ty [])    = gnest ("Type:" <$> pretty ty)
    pretty (OTyCheck ty holes) = group (nest' ("Holes:" <$> prettyList holes) <$>
                                        nest' ("Type:" <$> pretty ty))
    pretty (OPretty t)         = pretty t
    pretty (OHoles [])         = "OK"
    pretty (OHoles holes)      = gnest ("Holes:" <$> prettyList holes)
    pretty OOK                 = "OK"
    pretty OQuit               = "Bye!"
    pretty OSkip               = ""
    pretty OHelp               =
        "<decl>     Declare value/data type/record" <$$>
        ":e <term>  Normalise" <$$>
        ":p <term>  Pretty print" <$$>
        ":l <file>  Load file" <$$>
        ":r <file>  Reload file (erases previous environment)" <$$>
        ":q         Quit"
