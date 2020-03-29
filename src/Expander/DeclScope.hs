module Expander.DeclScope where

import Data.Unique

-- | A 'DeclValidityPtr' gets filled with a 'ScopeSet' representing an
-- environment. Each 'Scope' in this 'ScopeSet' corresponds to an identifier
-- which is bound in that environment, and the 'ScopeSet' indicates the phase
-- or phases in which each 'Scope' is valid.
--
-- Note that 'DeclValidityPtr' gets filled once we know which _names_ get
-- bound, the values to which they are bound may not be fully-expanded yet.
newtype DeclValidityPtr = DeclValidityPtr Unique
  deriving (Eq, Ord)

instance Show DeclValidityPtr where
  show (DeclValidityPtr u) = "(DeclValidityPtr " ++ show (hashUnique u) ++ ")"

