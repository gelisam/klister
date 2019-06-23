module Scope where


-- Int should be enough for now - consider bumping to something like int64
newtype Scope = Scope Int
  deriving (Eq, Ord, Show)

nextScope :: Scope -> Scope
nextScope (Scope i) = Scope (i + 1)
