{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Parser (readExpr, readModule) where

import Data.Char
import Data.Functor
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Text.Megaparsec
import Text.Megaparsec.Char (char)
import qualified Text.Megaparsec.Char.Lexer as L

import ModuleName
import Parser.Common
import Signals
import Syntax
import Syntax.Lexical
import Syntax.SrcLoc
import qualified ScopeSet



readModule :: FilePath -> IO (Either Text (ParsedModule Syntax))
readModule filename =
  do contents <- T.readFile filename
     name <- moduleNameFromPath filename
     case parse source filename contents of
       Left err -> pure $ Left $ T.pack $ errorBundlePretty err
       Right (lang, decls) ->
         pure $ Right $ ParsedModule { _moduleSource = name
                                     , _moduleLanguage = lang
                                     , _moduleContents = decls
                                     }
  where
    source = (,) <$> hashLang <*> manyStx expr <* eof

readExpr :: FilePath -> Text -> Either Text Syntax
readExpr filename fileContents =
  case parse (eatWhitespace *> expr <* eof) filename fileContents of
    Left err -> Left $ T.pack $ errorBundlePretty err
    Right ok -> Right ok

expr :: Parser Syntax
expr = list <|> ident <|> signal <|> bool <|> string <|> quoted <|> quasiquoted <|> unquoted

ident :: Parser Syntax
ident =
  do Located srcloc x <- lexeme identName
     return $ Syntax $ Stx ScopeSet.empty srcloc (Id x)

signal :: Parser Syntax
signal =
  do Located srcloc s <- lexeme signalNum
     return $ Syntax $ Stx ScopeSet.empty srcloc (Sig s)

list :: Parser Syntax
list = parenned "(" ")" <|> parenned "[" "]"
  where
    parenned open close =
      do Located loc1 _ <- located (literal open)
         xs <- many expr
         Located loc2 _ <- located (literal close)
         return $ Syntax $ Stx ScopeSet.empty (spanLocs loc1 loc2) (List xs)

manyStx :: Parser Syntax -> Parser Syntax
manyStx p =
  do Located loc xs <- located (many p)
     return $ Syntax $ Stx ScopeSet.empty loc (List xs)


bool :: Parser Syntax
bool =
  do Located loc b <- located (Bool <$> (true <|> false))
     return $ Syntax $ Stx ScopeSet.empty loc b
  where
    true  = (literal "#true" <|> literal "#t")  $> True
    false = (literal "#false" <|> literal "#f") $> False

string :: Parser Syntax
string =
  do Located loc s <- lexeme (String . T.pack <$> strChars)
     return $ Syntax $ Stx ScopeSet.empty loc s
  where
    strChars = char '"' *> strContents
    strContents = manyTill L.charLiteral (char '"')


hashLang :: Parser Syntax
hashLang =
  do literal "#lang"
     expr

quoted :: Parser Syntax
quoted =
  do Located loc1 _ <- lexeme (literal "'")
     e@(Syntax (Stx _ loc2 _)) <- expr
     return $ Syntax $ Stx ScopeSet.empty (spanLocs loc1 loc2) $
       List [ Syntax (Stx ScopeSet.empty loc1 (Id "quote"))
            , e
            ]

quasiquoted :: Parser Syntax
quasiquoted =
  do Located loc1 _ <- lexeme (literal "`")
     e@(Syntax (Stx _ loc2 _)) <- expr
     return $ Syntax $ Stx ScopeSet.empty (spanLocs loc1 loc2) $
       List [ Syntax (Stx ScopeSet.empty loc1 (Id "quasiquote"))
            , e
            ]

unquoted :: Parser Syntax
unquoted =
  do Located loc1 _ <- lexeme (literal ",")
     e@(Syntax (Stx _ loc2 _)) <- expr
     return $ Syntax $ Stx ScopeSet.empty (spanLocs loc1 loc2) $
       List [ Syntax (Stx ScopeSet.empty loc1 (Id "unquote"))
            , e
            ]


-- | The identifier rules from R6RS Scheme, minus hex escapes
identName :: Parser Text
identName =
  normalIdent <|> specialIdent <|> magicIdent

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

    magicIdent = (literal "#%app" $> "#%app")       <|>
                 (literal "#%module" $> "#%module")

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
lexeme p = located p <* eatWhitespace

located :: Parser a -> Parser (Located a)
located p =
  do SourcePos fn (unPos -> startL) (unPos -> startC) <- getSourcePos
     tok <- p
     SourcePos _ (unPos -> endL) (unPos -> endC) <- getSourcePos
     return (Located (SrcLoc fn (SrcPos startL startC) (SrcPos endL endC)) tok)


spanLocs :: SrcLoc -> SrcLoc -> SrcLoc
spanLocs (SrcLoc fn start _) (SrcLoc _ _ end) = SrcLoc fn start end
