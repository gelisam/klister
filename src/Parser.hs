{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Parser (readExpr, readModule) where

import Control.Monad
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
                                     , _moduleContents = addModule decls
                                     }
  where
    source = (,) <$> hashLang <*> manyStx expr <* eof
    addModule (Syntax (Stx scs loc (List decls)))
      = Syntax (Stx scs loc (List (module_ : decls)))
      where
        module_ = Syntax (Stx scs loc (Id "#%module"))
    addModule _
      = error "internal error: manyStx somehow didn't return a List"

readExpr :: FilePath -> Text -> Either Text Syntax
readExpr filename fileContents =
  case parse (eatWhitespace *> expr <* eof) filename fileContents of
    Left err -> Left $ T.pack $ errorBundlePretty err
    Right ok -> Right ok

expr :: Parser Syntax
expr = list <|> ident <|> integer <|> string <|> quoted <|> quasiquoted <|> unquote_spliced <|> unquoted

ident :: Parser Syntax
ident =
  do Located srcloc x <- lexeme identName
     return $ Syntax $ Stx ScopeSet.empty srcloc (Id x)

integer :: Parser Syntax
integer =
  do Located srcloc s <- lexeme integerNum
     return $ Syntax $ Stx ScopeSet.empty srcloc (Integer s)

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

unquote_spliced :: Parser Syntax
unquote_spliced =
  do Located loc1 _ <- lexeme (literal ",@")
     e@(Syntax (Stx _ loc2 _)) <- expr
     return $ Syntax $ Stx ScopeSet.empty (spanLocs loc1 loc2) $
       List [ Syntax (Stx ScopeSet.empty loc1 (Id "unquote-splicing"))
            , e
            ]

-- | Mostly like the identifier rules from R6RS Scheme, minus hex escapes
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
      try $
      do str <- chunk "+" <|> chunk "-" <|> chunk "..."
         more <- many subseq
         guard (null more || not (all isDigit more))
         return (str <> T.pack more)

    magicIdent = (literal "#%app" $> "#%app")
             <|> (literal "#%module" $> "#%module")
             <|> (literal "#%integer-literal" $> "#%integer-literal")
             <|> (literal "#%string-literal" $> "#%string-literal")

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


integerNum :: Parser Integer
integerNum = do
  sign <- optional (chunk "+" $> id <|> chunk "-" $> negate)
  maybe id id sign . read . T.unpack <$> takeWhile1P (Just "integer (digits)") isDigit

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
