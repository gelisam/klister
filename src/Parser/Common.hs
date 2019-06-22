{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Parser.Common (Parser, eatWhitespace, literal) where

import Data.Char
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Syntax
import Syntax.Lexical

type Parser = Parsec Void Text

eatWhitespace :: Parser ()
eatWhitespace = L.space space1 lineComment blockComment
  where
    lineComment = L.skipLineComment "--"
    blockComment = L.skipBlockComment "{-" "-}"

literal :: Text -> Parser ()
literal x = L.symbol eatWhitespace x *> pure ()
