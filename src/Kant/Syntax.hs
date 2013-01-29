{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Kant.Syntax where


data Id = Id String         -- ^ Original name
             Int            -- ^ Tag
    deriving (Eq)
instance Show Id where
    show (Id v t) = show (v ++ show t)

type ConId  = String
type Module = [Id]
type Level  = Int
data QName  = QName Module Id

data Decl
    = Val Id                     -- ^ Name
          Term
          [Branch]               -- ^ Branches, abstracted variables indexed by
                                 --   number, function itself is 0.
    | DataType
          Id                     -- ^ Name
          [Term]                 -- ^ Parameters' types
          Level                  -- ^ Resulting level
          [ConDecl]              -- ^ Constructors

data ConDecl = ConDecl ConId Term

type Branch = (ConId, [Id], Term)

data Term
    = Var Id
    | Con ConId
    | Set Level
    | App Term Term
    | Lambda Id Term Term
    deriving (Eq, Show)

subst :: Id -> Term -> Term -> Term
subst v t m@(Var v')      = if v == v' then t else m
subst v t (App m n)       = App (subst v t m) (subst v t n)
subst v t (Lambda v' m n) = Lambda v' (subst v t m)
                                   (if v == v' then n else subst v t n)
subst _ _ m               = m
