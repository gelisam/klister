module Core.Builder where

import qualified Data.Text as T
import Data.Unique


import Core
import ScopeSet ()
import Signals
import Syntax
import Syntax.SrcLoc

fakeLoc :: SrcLoc
fakeLoc = SrcLoc "<fake>" (SrcPos 0 0) (SrcPos 0 0)

fakeIdent :: Ident
fakeIdent = Stx mempty fakeLoc (T.pack "fake")

lam :: (IO Core -> IO Core) -> IO Core
lam f = do
  v <- Var <$> newUnique
  body <- f (pure (Core (CoreVar v)))
  return (Core (CoreLam fakeIdent v body))

app :: IO Core -> IO Core -> IO Core
app fun arg = Core
          <$> (CoreApp <$> fun <*> arg)

sig :: Int -> IO Core
sig s = return $ Core $ CoreSignal $ Signal s

sendSig :: Core -> IO Core
sendSig = return . Core . CoreSendSignal

waitSig :: Core -> IO Core
waitSig = return . Core . CoreWaitSignal

