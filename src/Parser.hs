{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Parser (readExpr) where

import Data.Char
import Data.Text (Text)
import qualified Data.Text as T

import Text.Megaparsec
import qualified Text.Megaparsec.Char.Lexer as L

import Parser.Common
import Signals
import Syntax
import Syntax.Lexical
import qualified ScopeSet


readExpr :: FilePath -> Text -> Either Text Syntax
readExpr filename fileContents =
  case parse (eatWhitespace *> expr <* eof) filename fileContents of
    Left err -> Left $ T.pack $ errorBundlePretty err
    Right ok -> Right ok

expr :: Parser Syntax
expr = list <|> vec <|> ident <|> signal

ident :: Parser Syntax
ident =
  do Located srcloc x <- lexeme identName
     return $ Syntax $ Stx ScopeSet.empty srcloc (Id x)

signal :: Parser Syntax
signal =
  do Located srcloc s <- lexeme signalNum
     return $ Syntax $ Stx ScopeSet.empty srcloc (Sig s)

list :: Parser Syntax
list =
  do Located loc1 _ <- located (literal "(")
     xs <- many expr
     Located loc2 _ <- located (literal ")")
     return $ Syntax $ Stx ScopeSet.empty (spanLocs loc1 loc2) (List xs)

vec  :: Parser Syntax
vec =
  do Located loc1 _ <- located (literal "[")
     xs <- many expr
     Located loc2 _ <- located (literal "]")
     return $ Syntax $ Stx ScopeSet.empty (spanLocs loc1 loc2) (Vec xs)

identName :: Parser Text
identName = takeWhile1P (Just "identifier character") isLetter

signalNum :: Parser Signal
signalNum = toSignal <$> takeWhile1P (Just "signal (digits)") isDigit
  where
    toSignal :: Text -> Signal
    toSignal = Signal . read . T.unpack

lexeme :: Parser a -> Parser (Located a)
lexeme = located . L.lexeme eatWhitespace

located :: Parser a -> Parser (Located a)
located p =
  do SourcePos fn (unPos -> startL) (unPos -> startC) <- getSourcePos
     tok <- p
     SourcePos _ (unPos -> endL) (unPos -> endC) <- getSourcePos
     return (Located (SrcLoc fn (SrcPos startL startC) (SrcPos endL endC)) tok)


spanLocs :: SrcLoc -> SrcLoc -> SrcLoc
spanLocs (SrcLoc fn start _) (SrcLoc _ _ end) = SrcLoc fn start end
