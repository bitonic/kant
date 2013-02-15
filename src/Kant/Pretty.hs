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
                  (<$>), vsep, group, (<$$>))
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
    pretty (SArr mn ty₁ ty₂) = l <+> "->" <+> noArr ty₂
      where
        l = case mn of
                Nothing -> noArr ty₁
                Just n  -> "(" <> typed n ty₁ <> ")"
        noArr t@(SApp _ _) = pretty t
        noArr t            = singleParens t
    pretty to@(SApp _ _) = go to
      where
        go (SApp t₁ t₂) = go t₁ <+> singleParens t₂
        go t           = singleParens t
    pretty (SLam pars t) =
        "\\" <> group (align (prettyPars' pars <> "=>" <$> align (pretty t)))
    pretty (SCase _ _ _) = undefined

nest :: Doc -> Doc
nest = PrettyPrint.nest 2

singleTerm :: STerm -> Bool
singleTerm t@(SVar _)  = True
singleTerm t@(SType _) = True
singleTerm t           = False

singleParens :: STerm -> Doc
singleParens t = if singleTerm t then pt else "(" <> align pt <> ")"
  where pt = pretty t

prettyPars :: [SParam] -> Doc
prettyPars [] = ""
prettyPars ((mns, ty) : pars) =
    case mns of
        Nothing -> singleParens ty
        Just ns -> "[" <> hsep' ns <+> ":" <+> pretty ty <> "]"
    <+> prettyPars pars

prettyPars' :: [SParam] -> Doc
prettyPars' pars = prettyPars pars <> spaceIfCons pars

prettyBarred :: (a -> Doc) -> [a] -> Doc
prettyBarred _ [] = "{ }"
prettyBarred f (x : xs) = vsep ("{" <+> f x : map (("|" <+>) . f) xs ++ ["}"])

typed :: Id -> STerm -> Doc
typed n ty = pretty n <+> ":" <+> pretty ty

instance Pretty Decl where
    pretty = pretty . (distill :: Decl -> SDecl)

instance Pretty SDecl where
    pretty (SVal n pars ty t) =
        group (end (nest (pretty n <+> prettyPars pars <> ":" <+> pretty ty
                          <+> "=>" <+> if single then pt else "(" <$$> pt)))
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

instance Pretty Module where
    pretty = pretty . (distill :: Module -> SModule)

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
    -- pretty (NotConstructor br) =
    --     group (nest ("Pattern matching on a non-constructor in branch" <$>
    --                  prettyBranch br))
    -- pretty (WrongArity br) =
    --     group (nest ("Branch gives wrong number of arguments to constructor" <$>
    --                  prettyBranch br))

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
