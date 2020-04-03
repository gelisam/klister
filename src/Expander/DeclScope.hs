module Expander.DeclScope where

import Data.Unique

-- | A 'DeclValidityPtr' gets filled with a 'ScopeSet' consisting of all the
-- scopes introduced by a declaration or a declaration group, so that later
-- code can see the identifiers they bind.
--
-- Note that 'DeclValidityPtr' gets filled once we know which _names_ get
-- bound, the values to which they are bound may not be fully-expanded yet.
newtype DeclValidityPtr = DeclValidityPtr Unique
  deriving (Eq, Ord)

instance Show DeclValidityPtr where
  show (DeclValidityPtr u) = "(DeclValidityPtr " ++ show (hashUnique u) ++ ")"

