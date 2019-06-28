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

-- | The identifier rules from R6RS Scheme, minus hex escapes
identName :: Parser Text
identName =
  normalIdent <|> specialIdent

  where
    normalIdent :: Parser Text
    normalIdent =
      do c1 <- initial
         cs <- many subseq
         return (T.pack (c1 : cs))

    specialIdent :: Parser Text
    specialIdent =
      do str <- chunk "+" <|> chunk "-" <|> chunk "..."
         more <- many subseq
         return (str <> T.pack more)

    initial :: Parser Char
    initial =
      satisfy (\c -> isConstituent c || isSpecialInit c) <?>
      "identifier-initial character"

    subseq :: Parser Char
    subseq =
      satisfy (\c ->
                 isConstituent c ||
                 isSpecialInit c ||
                 isDigit c ||
                 generalCategory c `elem` subseqCats ||
                 c `elem` ("+-.@" :: [Char])) <?> "identifier subsequent character"

    isConstituent c =
      c `elem` alphabet ||
      c `elem` (map toUpper alphabet) ||
      (ord c > 126 && generalCategory c `elem` constituentCats)
    alphabet = "abcdefghijklmnopqrstuvwxyz"
    isSpecialInit c = c `elem` ("!$%&*/:<=>?^_~" :: [Char])

    constituentCats = [UppercaseLetter, LowercaseLetter, TitlecaseLetter, ModifierLetter, OtherLetter, NonSpacingMark, LetterNumber, OtherNumber, DashPunctuation, ConnectorPunctuation, OtherPunctuation, CurrencySymbol, MathSymbol, ModifierSymbol, OtherSymbol, PrivateUse]

    subseqCats = [DecimalNumber, SpacingCombiningMark, EnclosingMark]


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
