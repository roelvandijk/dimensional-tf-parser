{-# LANGUAGE FlexibleContexts
           , NoImplicitPrelude
           , PackageImports
           , UnicodeSyntax
  #-}

module Numeric.Units.Dimensional.TF.Parser.Unit
    ( UnitExp(..)
    , parseUnitExp
    ) where

--------------------------------------------------------------------------------
-- Imports
--------------------------------------------------------------------------------

import "base" Control.Applicative ( (<*>), (<*), (*>), pure )
import "base" Data.Bool           ( Bool(False, True) )
import "base" Data.Either         ( Either(Left, Right) )
import "base" Data.Function       ( ($), id )
import "base" Data.Functor        ( (<$>), (<$) )
import "base" Data.List           ( foldl' )
import "base" Data.Maybe          ( Maybe(Nothing, Just) )
import "base" Data.String         ( String )
import "base" Prelude             ( Num, (+), negate )
import "base" Text.Show           ( Show )
import "base-unicode-symbols" Prelude.Unicode ( ℤ, (⋅) )
import "parsec" Text.Parsec.Char       ( char, letter, oneOf )
import "parsec" Text.Parsec.Combinator ( many1, eof, choice )
import "parsec" Text.Parsec.Error
    ( ParseError, Message(Message), newErrorMessage )
import "parsec" Text.Parsec.Expr
    ( Assoc(AssocLeft, AssocRight), Operator(Infix), buildExpressionParser )
import "parsec" Text.Parsec.Language ( emptyDef )
import "parsec" Text.Parsec.Pos      ( initialPos )
import "parsec" Text.Parsec.Prim
    ( Parsec, parse, (<|>), (<?>), try )
import qualified "parsec" Text.Parsec.Token as P
import "transformers" Data.Functor.Identity ( Identity )


--------------------------------------------------------------------------------
-- Language of Physical Units
--------------------------------------------------------------------------------

-- | Expressions of physical units.
data UnitExp =
      UEName String          -- "metre"
    | UEMul  UnitExp UnitExp -- "newton * metre"
    | UEDiv  UnitExp UnitExp -- "metre / second"
    | UEPow  UnitExp ℤ       -- "metre ^ 3"
      deriving Show

infixr 8 `UEPow`
infixl 7 `UEMul`
infixl 7 `UEDiv`

-- | Less strict version of the language that is easier to
-- parse. Allows nonsensical things with the power operator and with
-- integer literals.
data UnitExpRaw =
      UERName String               -- "metre"
    | UERInt ℤ                     -- "3"
    | UERMul UnitExpRaw UnitExpRaw -- "newton * metre"
    | UERDiv UnitExpRaw UnitExpRaw -- "metre / second"
    | UERPow UnitExpRaw UnitExpRaw -- "metre ^ 3"
      deriving Show

infixr 8 `UERPow`
infixl 7 `UERMul`
infixl 7 `UERDiv`

convertRawExp ∷ UnitExpRaw → Maybe UnitExp
convertRawExp (UERName n)  = Just $ UEName n
convertRawExp (UERInt _)   = Nothing
convertRawExp (UERMul x y) = UEMul <$> convertRawExp x <*> convertRawExp y
convertRawExp (UERDiv x y) = UEDiv <$> convertRawExp x <*> convertRawExp y
convertRawExp (UERPow x (UERInt i)) = (`UEPow` i) <$> convertRawExp x
convertRawExp (UERPow _ _) = Nothing

--------------------------------------------------------------------------------
-- Lexer
--------------------------------------------------------------------------------

unitDef ∷ P.LanguageDef st
unitDef = emptyDef
          { P.commentStart    = ""
          , P.commentEnd      = ""
          , P.commentLine     = ""
          , P.nestedComments  = False
          , P.identStart      = P.identLetter unitDef
          , P.identLetter     = letter
          , P.opStart         = P.opLetter unitDef
          , P.opLetter        = oneOf ['*', '·', '/', '^']
          , P.reservedNames   = []
          , P.reservedOpNames = []
          , P.caseSensitive   = True
          }

lexer ∷ P.GenTokenParser String u Identity
lexer = P.makeTokenParser unitDef


--------------------------------------------------------------------------------
-- Unit parser
--------------------------------------------------------------------------------

parseUnitExp ∷ String → Either ParseError UnitExp
parseUnitExp str =
    case parse (unitExp <* eof) "" str of
      Left err → Left err
      Right uer →
        case convertRawExp uer of
          Just ue → Right ue
          Nothing → Left $ newErrorMessage (Message "Illegal expression")
                                           (initialPos "")

unitExp ∷ Parsec String () UnitExpRaw
unitExp = buildExpressionParser table term
  where
    table = [ [ binOp "^" UERPow AssocRight ]
            , [ binOp "*" UERMul AssocLeft
              , binOp "·" UERMul AssocLeft
              , binOp "/" UERDiv AssocLeft
              ]
            ]
    term = (P.parens lexer unitExp <?> "group")
         <|> try (UERPow <$> unitName <*> unitSuperExp)
         <|> unitName
         <|> UERInt <$> P.integer lexer

    unitName = UERName <$> (P.identifier lexer <?> "unit name")
    unitSuperExp = UERInt <$> (P.lexeme lexer superDecimal <?> "superscript decimal")

    binOp name fun assoc = Infix (P.reservedOp lexer name *> pure fun) assoc

superDecimal ∷ (Num α) ⇒ Parsec String () α
superDecimal =
  superSign <*> (foldl' (\x d → 10⋅x + d) 0 <$> many1 superDigit)

superDigit ∷ (Num α) ⇒ Parsec String () α
superDigit = choice
             [ 0 <$ char '⁰'
             , 1 <$ char '¹'
             , 2 <$ char '²'
             , 3 <$ char '³'
             , 4 <$ char '⁴'
             , 5 <$ char '⁵'
             , 6 <$ char '⁶'
             , 7 <$ char '⁷'
             , 8 <$ char '⁸'
             , 9 <$ char '⁹'
             ]

superSign ∷ (Num α) ⇒ Parsec String () (α → α)
superSign =   (char '⁻' *> pure negate)
          <|> (char '⁺' *> pure id)
          <|> pure id

-- tests ∷ [String]
-- tests = map (\s → s ++ "\n" ++ show (parseUnitExp s) ++ "\n")
--   [ "a"
--   , "(a"
--   , "a)"
--   , "(a)"
--   , "((c))"
--   , "d/e"
--   , "((f)/(g))"
--   , "h^1 * i^-1"
--   , "j·k⁻¹"
--   , "l/(m·m)"
--   , "n/o²"
--   , "x^3"
--   , "x³"
--   , "m² · kg · s⁻³ · A⁻²" -- Ω
--   , "m/s·s"
--   , "m/(s·s)"
--   , "m/s^2"
--   , "m/s²"
--   , "x / y / z "
--   , "m * s * m"
--     -- These should fail:
--   , "(m/s)²"
--   , "a @@@@"
--   , "2"
--   , "2/3"
--   , "m^s"
--   ]
