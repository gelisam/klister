{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Parser.Common (Parser, eatWhitespace, literal) where

import Data.Text (Text)
import Data.Void

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L


type Parser = Parsec Void Text

eatWhitespace :: Parser ()
eatWhitespace = L.space space1 lineComment blockComment
  where
    lineComment = L.skipLineComment "--"
    blockComment = L.skipBlockComment "{-" "-}"

literal :: Text -> Parser ()
literal x = L.symbol eatWhitespace x *> pure ()
