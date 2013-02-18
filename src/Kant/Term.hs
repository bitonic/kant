{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Kant.Term
    ( -- * Abstract syntax tree
      Id
    , ConId
    , Level
    , Module(..)
    , Decl(..)
    , Data(..)
    , Constr
    , Param
    , TermT(..)
    , Term
    , CaseT(..)
    , BranchT(..)
    , FixT(..)
    , TName
    , TScope
    , discarded
      -- * Smart constructors
    , lam
    , lams
    , pi_
    , pis
    , fix
    , arr
    , case_
    , app
    , params
      -- * Utilities
    , unrollApp
    , unrollArr
    , unrollArr'
    , arrLen
    , instantiateList
    , instantiateNatU
    , scopeVars
    , scopeVar
    , moduleNames
    , discardedM
    ) where

import           Control.Applicative (Applicative(..), (<$>))
import           Control.Arrow (second)
import           Control.Monad (ap, liftM)
import           Data.Foldable (Foldable)
import           Data.Maybe (listToMaybe, fromMaybe)
import           Data.Traversable (Traversable)
import           Prelude hiding ((!!), length)

import qualified Data.Set as Set

import           Bound
import           Bound.Name
import           Bound.Scope
import           Numeric.Natural
import           Prelude.Extras

import           Kant.Common

{-
t     Term
ty    Terms that are types
v     Name
n     Id inside Name and Id in general
con   Constr
c     constructor Id
l     Level
s     Scope
br    Branch
i     For numbers, e.g. the number of things in patterns
par   Parameter
d     Data
env   Env
-}

newtype Module = Module {unModule :: [Decl]}
    deriving (Show, Eq)

-- TODO we can remove the type in ValD, since Fix include the recursive type
-- | Value or datatype declaration
data Decl
    = Val Id Term
    | DataD Data
    | Postulate Id Term
    deriving (Show, Eq)

-- | Inductive data types declarations.
--
--   The parameters stuff is basically an arrow type and in fact we could simply
--   use a 'Term', but I want to enforce more easily the fact that the return
--   type is either always a 'Type'n with type constructors or whatever the
--   datatype we are defining is with data constructors.  'dataDecl' can be used
--   to recover the types.
--
--   Note that each parameter is scoped through the rest of the list.  This
--   means that parameters in data constructors can shadow global parameters in
--   the type constructor.
data Data = Data ConId            -- Name
                 [Param]          -- Parameters' types
                 Level            -- Resulting level
                 [Constr]         -- Constructors
    deriving (Show, Eq)

type Constr = (ConId, [Param])
type Param = (Id, Term)

-- | A 'Name' with an 'Id' name.
type TName a = Name Id a

-- | Simple scope with one variable abstracted
type TScope a = Scope (TName ()) TermT a

-- | Terms for our language.  This is what we typecheck and reduce.
data TermT a
    = Var a
      -- | The type of types
    | Type Level
      -- | Function application.  To the left we expect either a 'Lam' or a
      --   'Fix'.
    | App (TermT a) (TermT a)
      -- | Constructor for arrow types, of type @(A : Type n) -> (A -> Type m) ->
      --   Type (n ⊔ m)@.
    | Arr (TermT a) (TScope a)
      -- | Lambda abstraction.
    | Lam (TermT a) (TScope a)
      -- | Pattern matching.
    | Case (TermT a)            -- Thing to pattern match (scrutined).
           (CaseT TermT a)
      -- | An instance of some inductive data type created by the user.
    | Constr ConId              -- Constructor
             [TermT a]          -- Type parameters
             [TermT a]          -- Data Parameters
    | Fix (TermT a)             -- Type of the rec function.
          (FixT TermT a)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

type Term = TermT Id

instance Eq1 TermT   where (==#)      = (==)
instance Ord1 TermT  where compare1   = compare
instance Show1 TermT where showsPrec1 = showsPrec
instance Read1 TermT where readsPrec1 = readsPrec
instance Applicative TermT where pure = Var; (<*>) = ap

instance Monad TermT where
    return = Var

    Var v           >>= f = f v
    Type l          >>= _ = Type l
    App t₁ t₂       >>= f = App (t₁ >>= f) (t₂ >>= f)
    Arr ty s        >>= f = Arr (ty >>= f) (s >>>= f)
    Lam t s         >>= f = Lam (t >>= f) (s >>>= f)
    Case t s        >>= f = Case (t >>= f) (s >>>= f)
    Constr c tys ts >>= f = Constr c (map (>>= f) tys) (map (>>= f) ts)
    Fix ty s        >>= f = Fix (ty >>= f) (s >>>= f)

data CaseT f a =
    CaseT (Scope (TName ()) f a) -- The type of the result, abstracted over the
                                 -- scrutined.
          [BranchT f a]
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

instance Bound CaseT where
    CaseT s brs >>>= f = CaseT (s >>>= f) (map (>>>= f) brs)

abstractCase :: (Monad f) => Id -> f Id -> [(ConId, [Id], f Id)] -> CaseT f Id
abstractCase n ty brs =
    CaseT (abstract1Name n ty) [abstractBranch n c ns t | (c, ns, t) <- brs]

data BranchT f a =
    BranchT -- Constructor to match
            ConId
            -- Number of arguments.  INVARIANT: in the scope below all bound
            -- 'Natural's are less than this 'Natural'.
            Natural
            -- The scope matching the arguments of the constructor, and the
            -- refined scrutined.
            (Scope (TName Natural) (Scope (TName ()) f) a)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

abstractBranch :: (Monad f)
               => Id            -- ^ Scrutined variable
               -> ConId         -- ^ Matching constructor
               -> [Id]          -- ^ Variables of the constructor
               -> f Id          -- ^ Body
               -> BranchT f Id
abstractBranch n c ns t =
    BranchT c (length ns) (abstractName (`elemIndex` ns) (abstract1Name n t))

instance Bound BranchT where
    BranchT c i (Scope s) >>>= f = BranchT c i (Scope (liftM (>>>= f) `liftM` s))
-- type Branch = BranchT Id

data FixT f a =
    FixT -- Number of arguments. INVARIANT: in the scope below all bound
         -- 'Natural's are less than this 'Natural'.
         Natural
         -- Body, scoped with the arguments (there should be as many as the
         -- length of the list) and the recursive function.
         (Scope (TName Natural) (Scope (TName ()) f) a)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

instance Bound FixT where
    FixT i (Scope s) >>>= f = FixT i (Scope (liftM (>>>= f) `liftM` s))

abstractFix :: (Monad f)
            => Id               -- ^ Name of the recursor
            -> [Id]             -- ^ Arguments names
            -> f Id             -- ^ Body
            -> FixT f Id
abstractFix n ns t =
    FixT (length ns) (abstractName (`elemIndex` ns) (abstract1Name n t))

-- | A binding/pattern match that we are not going to use.
discarded :: Id
discarded = "_"

-- | Good 'ol lambda abstraction.
lam :: Id -> Term -> Term -> Term
lam v ty t = Lam ty (abstract1Name v t)

-- | Folds a list of parameters.
params :: (Id -> Term -> Term -> Term) -> [Param] -> Term -> Term
params f pars t = foldr (\(v, t₁) t₂ -> f v t₁ t₂) t pars

-- | Like 'lam', but abstracts over several parameters
lams :: [Param] -> Term -> Term
lams = params lam

-- | Pattern matching.
case_ :: Term                   -- ^ The scrutined
      -> Id                     -- ^ The abstracted var
      -> Term                   -- ^ The return type
      -> [(ConId, [Id], Term)]  -- ^ Each branch has a constructor, bound
                                --   variables, and a body.
      -> Term
case_ t n ty brs = Case t (abstractCase n ty brs)

-- | Dependent function, @(x : A) -> B@.
pi_ :: Id                       -- ^ Abstracting an @x@...
    -> Term                     -- ^ ...of type @A@..
    -> Term                     -- ^ ...over type @B@
    -> Term
pi_ v ty₁ ty₂ = Arr ty₁ (abstract1Name v ty₂)

-- | @lam : lams = pi_ : pis@.
pis :: [Param] -> Term -> Term
pis = params pi_

fix :: Id                       -- ^ Name of the recursor
    -> [Param]                  -- ^ Arguments
    -> Term                     -- ^ Return type
    -> Term                     -- ^ Body
    -> Term
fix n pars ty t = Fix (pis pars ty) (abstractFix n (map fst pars) t)

-- | Non-dependent function, @A -> B@
arr :: Term -> Term -> Term
arr ty₁ ty₂ = Arr ty₁ (toScope (F <$> ty₂))

-- | @app a b c@ will return the term corresponding to @a b c@, i.e. @a@ applied
--   to @b@ applied to @c@.  Fails with empty lists.
app :: [TermT a] -> TermT a
app = foldl1 App

-- | Dual of 'app'.
unrollApp :: TermT a -> (TermT a, [TermT a])
unrollApp (App t₁ t₂) = second (++ [t₂]) (unrollApp t₁)
unrollApp t           = (t, [])

-- | Dual of 'pi_' (but with more general types).
unrollArr' :: (Id -> a) -> Natural -> TermT a -> Maybe ([(a, TermT a)], TermT a)
unrollArr' nest i (Arr ty s) | i > 0 =
    do (pars, ty') <- unrollArr' nest (i - 1) (instantiate1 (Var n) s)
       return ((n, ty) : pars, ty')
  where
    n = case bindings s of
            []     -> nest discarded
            (n':_) -> nest (name n')
unrollArr' _ i t = if i == 0 then Just ([], t) else Nothing

-- | A more specific 'unrollArr''.
unrollArr :: Natural -> Term -> Maybe ([Param], Term)
unrollArr = unrollArr' id

arrLen :: TermT a -> Natural
arrLen (Arr _ s) = 1 + arrLen (fromScope s)
arrLen _         = 0

-- | Returns the names found in a 'Scope' that binds them.
scopeVars :: (Monad f, Foldable f, Ord n) => Scope (Name n b) f a -> [n]
scopeVars s = Set.toList (Set.fromList (map name (bindings s)))

-- | Returns a name if one variable is found.
scopeVar :: (Monad f, Foldable f, Ord n) => Scope (Name n ()) f a -> Maybe n
scopeVar = listToMaybe . scopeVars

-- | Instantiates an 'Natural'-indexed scope where each number 'n' is replaced
--   by the element at index 'n' in the provided list.
--
--   INVARIANT All the bound 'Natural' are less than the length of the list.
instantiateList :: Monad f => [f a] -> Scope (TName Natural) f a -> f a
instantiateList ts = instantiateName (ts !!)

-- | Instantiate the '()' and the 'Natural' at once.
instantiateNatU :: Monad f
                => [f a] -> f a -> Scope (TName Natural) (Scope (TName ()) f) a -> f a
instantiateNatU ts t ss =
    instantiate1 t (instantiateList (map (toScope . liftM F) ts) ss)

moduleNames :: Module -> [Id]
moduleNames = concatMap go . unModule
  where
    go (Val n _)                   = [n]
    go (Postulate n _)             = [n]
    go (DataD (Data tyc _ _ cons)) = tyc : map fst cons

-- | Returns 'discarded' if the argument is nothing.
discardedM :: Maybe Id -> Id
discardedM = fromMaybe discarded
