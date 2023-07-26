{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Expander.DeclScope where

import Unique
import Util.Key

-- | A 'DeclOutputScopesPtr' gets filled with a 'ScopeSet' consisting of all the
-- scopes introduced by a declaration or a declaration group, so that later code
-- can see the identifiers they bind.
--
-- Note that 'DeclOutputScopesPtr' gets filled once we know which _names_ get
-- bound, the values to which they are bound may not be fully-expanded yet.
newtype DeclOutputScopesPtr = DeclOutputScopesPtr Unique
  deriving newtype (Eq, Ord, HasKey)

instance Show DeclOutputScopesPtr where
  show (DeclOutputScopesPtr u) = "(DeclOutputScopesPtr " ++ show (hashUnique u) ++ ")"

