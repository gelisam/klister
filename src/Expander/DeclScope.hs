module Expander.DeclScope where

import Data.Unique

-- | A 'DeclValidityPtr' gets filled once we know at which phases an identifier
-- is bound (but before we know exactly what it is that this identifier is
-- bound to). In order to determine what a given identifier means, we must wait
-- until all the declarations listed earlier in the file have had their
-- 'DeclValidityPtr's filled.
newtype DeclValidityPtr = DeclValidityPtr Unique
  deriving (Eq, Ord)

instance Show DeclValidityPtr where
  show (DeclValidityPtr u) = "(DeclValidityPtr " ++ show (hashUnique u) ++ ")"

