module Core.Builder where

import qualified Data.Text as T
import Data.Unique


import Core
import ScopeSet ()
import Syntax

fakeLoc :: SrcLoc
fakeLoc = SrcLoc "<fake>" (SrcPos 0 0) (SrcPos 0 0)

fakeIdent :: Ident
fakeIdent = Stx mempty fakeLoc (T.pack "fake")

lam :: (Core -> IO Core) -> IO Core
lam f = do
  v <- Var <$> newUnique
  body <- f (Core (CoreVar v))
  return (Core (CoreLam fakeIdent v body))
