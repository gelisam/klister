{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Parser.Command (Command(..), readCommand) where

import Data.Char
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Parser.Common

data Command = Command_Quit
  deriving (Eq, Ord, Show, Read)

readCommand :: FilePath -> Text -> Either Text Command
readCommand filename fileContents =
  case parse (char ':' *> command <* eof) filename fileContents of
    Left err -> Left $ T.pack $ errorBundlePretty err
    Right ok -> Right ok

command :: Parser Command
command = Command_Quit <$ literal "q"
