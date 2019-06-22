{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Parser (readExpr) where

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

readExpr :: FilePath -> Text -> Either Text Syntax
readExpr filename fileContents =
  case parse (eatWhitespace *> expr <* eof) filename fileContents of
    Left err -> Left $ T.pack $ errorBundlePretty err
    Right ok -> Right ok

syntactically :: Parser a -> Parser (Stx a)
syntactically p =
  do (Located srcloc x) <- located p
     pure (Stx noScopes srcloc x)

expr :: Parser Syntax
expr = list <|> vec <|> identExpr
  where
    identExpr =
      do Located srcloc x <- lexeme ident
         return $ Syntax $ Stx noScopes srcloc (Id x)

list :: Parser Syntax
list =
  do Located loc1 _ <- located (literal "(")
     xs <- many expr
     Located loc2 _ <- located (literal ")")
     return $ Syntax $ Stx noScopes (spanLocs loc1 loc2) (List xs)

vec  :: Parser Syntax
vec =
  do Located loc1 _ <- located (literal "[")
     xs <- many expr
     Located loc2 _ <- located (literal "]")
     return $ Syntax $ Stx noScopes (spanLocs loc1 loc2) (Vec xs)

ident :: Parser Text
ident = takeWhile1P (Just "identifier character") isLetter

eatWhitespace :: Parser ()
eatWhitespace = L.space space1 lineComment blockComment
  where
    lineComment = L.skipLineComment "--"
    blockComment = L.skipBlockComment "{-" "-}"

literal :: Text -> Parser ()
literal x = L.symbol eatWhitespace x *> pure ()



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
