{-# LANGUAGE FlexibleContexts
           , NoImplicitPrelude
           , PackageImports
           , ScopedTypeVariables
           , TupleSections
           , UnicodeSyntax
  #-}

module Numeric.Units.Dimensional.TF.Parser.Unit where

--------------------------------------------------------------------------------
-- Imports
--------------------------------------------------------------------------------

import "base" Control.Applicative ( (<*>), (<*), (*>), (<|>), pure )
import qualified "base" Control.Arrow as Arr ( second )
import "base" Control.Monad ( return, sequence )
import "base" Data.Bool     ( Bool(False, True), not )
import "base" Data.Char     ( Char, isSpace )
import "base" Data.Either   ( Either(Left, Right), either )
import "base" Data.Eq       ( Eq )
import "base" Data.Function ( ($), id )
import "base" Data.Functor  ( (<$>), (<$) )
import "base" Data.Int      ( Int )
import "base" Data.List     ( (++), map, foldl', foldr, null, concat
                            , filter, find, intercalate, dropWhile, break
                            , genericReplicate
                            )
import "base" Data.Maybe    ( Maybe(Nothing, Just), maybe )
import "base" Data.Ord      ( Ord )
import "base" Data.String   ( String )
import "base" Data.Tuple    ( fst, snd, uncurry )
import "base" Prelude
    ( Num, Fractional, Floating, Double
    , (+), (-), (*), (/), (^^), error, abs, signum, negate, fromInteger, fromIntegral
    )
import "base" Text.Read     ( Read, reads, lex )
import "base" Text.Show     ( Show, show )
import "base-unicode-symbols" Data.Eq.Unicode       ( (≡), (≢) )
import "base-unicode-symbols" Data.Function.Unicode ( (∘) )
import "base-unicode-symbols" Prelude.Unicode       ( ℤ, ℚ, (⊥), (⋅) )
import "containers" Data.Map ( Map )
import qualified "containers" Data.Map as Map
    ( empty, assocs, findWithDefault, map, insert, insertWith, unionWith )
import qualified "dimensional-tf" Numeric.Units.Dimensional.TF as Dim -- ( (*) )
import "dimensional-tf" Numeric.Units.Dimensional.TF
    ( (*~), Quantity, Unit, Dim, prefix
    , DOne, one, DLength, DMass, DTime, DElectricCurrent
    , DThermodynamicTemperature, DAmountOfSubstance, DLuminousIntensity
    )
import "dimensional-tf" Numeric.Units.Dimensional.TF.SIUnits
import "dimensional-tf" Numeric.Units.Dimensional.TF.NonSI
import "mtl" Control.Monad.Error.Class ( MonadError, throwError )
import "numtype-tf" Numeric.NumType.TF
    ( NumType, Zero, toNum, pos1, pos2, pos3, pos4, neg1, neg2, neg3 )
import "parsec" Text.Parsec.Char       ( char, letter, oneOf, string )
import "parsec" Text.Parsec.Combinator ( many1, eof, choice )
import "parsec" Text.Parsec.Error
    ( ParseError, Message(Message), newErrorMessage )
import "parsec" Text.Parsec.Expr
    ( Assoc(AssocLeft, AssocRight), Operator(Infix), OperatorTable
    , buildExpressionParser
    )
import "parsec" Text.Parsec.Language ( emptyDef )
import "parsec" Text.Parsec.Pos      ( initialPos )
import "parsec" Text.Parsec.Prim
    ( Parsec, parse, (<?>), try )
import qualified "parsec" Text.Parsec.Token as P
import "transformers" Data.Functor.Identity ( Identity )


-- DEBUG
--import Prelude

--------------------------------------------------------------------------------
-- Products of powers of dimensions.
--------------------------------------------------------------------------------

-- | A 7-tuple containing the powers of the 7 base SI dimensions.
data DimPows = DimPows ℤ ℤ ℤ ℤ ℤ ℤ ℤ deriving (Eq, Ord, Show)

prettyDimPows ∷ DimPows → String
prettyDimPows (DimPows 0 0 0 0 0  0 0) = "dimensionless"
prettyDimPows (DimPows l m t i th n j) =
    concat $ filter (not ∘ null)
                    [ f l "L"
                    , f m "M"
                    , f t "T"
                    , f i "I"
                    , f th "Θ"
                    , f n "N"
                    , f j "J"
                    ]
  where
    f ∷ ℤ → String → String
    f 0 _ = ""
    f n sym = sym ++ map super (show n)

    super ∷ Char → Char
    super '-' = '⁻'
    super '0' = '⁰'
    super '1' = '¹'
    super '2' = '²'
    super '3' = '³'
    super '4' = '⁴'
    super '5' = '⁵'
    super '6' = '⁶'
    super '7' = '⁷'
    super '8' = '⁸'
    super '9' = '⁹'
    super c = c

instance Num DimPows where
    (+)    = dimValBinOp (+)
    (*)    = dimValBinOp (*)
    (-)    = dimValBinOp (-)
    negate = dimValUnOp negate
    abs    = dimValUnOp abs
    signum = dimValUnOp signum
    fromInteger n = DimPows n n n n n n n

dimValUnOp ∷ (ℤ → ℤ) → DimPows → DimPows
dimValUnOp f (DimPows l m t i th n j) =
    DimPows (f l) (f m) (f t) (f i) (f th) (f n) (f j)

dimValBinOp ∷ (ℤ → ℤ → ℤ) → DimPows → DimPows → DimPows
dimValBinOp f (DimPows l₁ m₁ t₁ i₁ th₁ n₁ j₁)
              (DimPows l₂ m₂ t₂ i₂ th₂ n₂ j₂) =
    DimPows (f l₁ l₂)
            (f m₁ m₂)
            (f t₁ t₂)
            (f i₁ i₂)
            (f th₁ th₂)
            (f n₁ n₂)
            (f j₁ j₂)


--------------------------------------------------------------------------------
-- Language of Physical Units
--------------------------------------------------------------------------------

data UnitExpParsed =
      UENameP String DimPows
    | UEPrefixP ℚ UnitExpParsed
    | UEIntP ℤ
    | UEMulP UnitExpParsed UnitExpParsed
    | UEDivP UnitExpParsed UnitExpParsed
    | UEPowP UnitExpParsed UnitExpParsed
      deriving Show

data UnitExp =
      UEName String DimPows
    | UEPrefix ℚ UnitExp
    | UEMul UnitExp UnitExp
    | UEDiv UnitExp UnitExp
    | UEPow UnitExp ℤ
      deriving (Eq, Show)

infixr 8 `UEPowP`, `UEPow`
infixl 7 `UEMulP`, `UEMul`
infixl 7 `UEDivP`, `UEDiv`

unitExpDimPows ∷ UnitExp → DimPows
unitExpDimPows = go
  where
    go (UEName _ d) = d
    go (UEPrefix _ x) = go x
    go (UEMul x y) = go x + go y
    go (UEDiv x y) = go x - go y
    go (UEPow x i) = go x ⋅ fromInteger i

convertParsedExp ∷ UnitExpParsed → Maybe UnitExp
convertParsedExp = go
  where
    go (UENameP n dim)       = Just $ UEName n dim
    go (UEPrefixP pf x)      = UEPrefix pf <$> go x
    go (UEIntP _)            = Nothing
    go (UEMulP x y)          = UEMul <$> go x <*> go y
    go (UEDivP x y)          = UEDiv <$> go x <*> go y
    go (UEPowP x (UEIntP i)) = (`UEPow` i) <$> go x
    go (UEPowP _ _)          = Nothing


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
        case convertParsedExp uer of
          Just ue → Right ue
          Nothing → Left $ newErrorMessage (Message "Illegal expression")
                                           (initialPos "")

unitExp ∷ Parsec String () UnitExpParsed
unitExp = buildExpressionParser table term
  where
    table ∷ OperatorTable String () Identity UnitExpParsed
    table = [ [ binOp "^" UEPowP AssocRight ]
            , [ binOp "*" UEMulP AssocLeft
              , binOp "·" UEMulP AssocLeft
              , binOp "/" UEDivP AssocLeft
              ]
            ]

    term ∷ Parsec String () UnitExpParsed
    term = (P.parens lexer unitExp)
         <|> try (UEPowP <$> unitName <*> unitSuperExp)
         <|> P.lexeme lexer unitName
         <|> UEIntP <$> P.integer lexer

-- [prefix_name] unit_name | [prefix_symbol] unit_symbol
unitName ∷ Parsec String () UnitExpParsed
unitName = try onlyNames <|> onlySymbols
  where
    onlyNames   = unit siPrefixNames   unitNames
    onlySymbols = unit siPrefixSymbols unitSymbols

    unitNames   = baseUnitNames   ++ map (Arr.second unitExpDimPows) derivedUnitNames
    unitSymbols = baseUnitSymbols ++ map (Arr.second unitExpDimPows) derivedUnitSymbols

    unit prefixTable unitTable =
        try (prefixedUnit prefixTable unitTable)
        <|> unitName unitTable

    prefixedUnit prefixTable unitTable = UEPrefixP <$> prefix prefixTable <*> unitName unitTable
    prefix tab = choice $ map (try ∘ (\(s, x) → string s *> pure x)) tab
    unitName tab = uncurry UENameP <$> choice (map (\t → try (string (fst t) *> pure t)) tab)

unitSuperExp ∷ Parsec String () UnitExpParsed
unitSuperExp = UEIntP <$> (P.lexeme lexer superDecimal <?> "superscript decimal")

binOp ∷ String → (α → α → α) → Assoc → Operator String () Identity α
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


--------------------------------------------------------------------------------
-- SI prefixes
--------------------------------------------------------------------------------

siPrefixNames ∷ (Fractional α) ⇒ [(String, α)]
siPrefixNames =
  [ ("yotta", 10 ^^   24)
  , ("zetta", 10 ^^   21)
  , ("exa",   10 ^^   18)
  , ("peta",  10 ^^   15)
  , ("tera",  10 ^^   12)
  , ("giga",  10 ^^    9)
  , ("mega",  10 ^^    6)
  , ("kilo",  10 ^^    3)
  , ("hecto", 10 ^^    2)
  , ("deca",  10 ^^    1)
  , ("deka",  10 ^^    1)
  , ("deci",  10 ^^ (- 1))
  , ("centi", 10 ^^ (- 2))
  , ("milli", 10 ^^ (- 3))
  , ("micro", 10 ^^ (- 6))
  , ("nano",  10 ^^ (- 9))
  , ("pico",  10 ^^ (-12))
  , ("femto", 10 ^^ (-15))
  , ("atto",  10 ^^ (-18))
  , ("zepto", 10 ^^ (-21))
  , ("yocto", 10 ^^ (-24))
  ]

siPrefixSymbols ∷ (Fractional α) ⇒ [(String, α)]
siPrefixSymbols =
  [ ("Y",  10 ^^   24)
  , ("Z",  10 ^^   21)
  , ("E",  10 ^^   18)
  , ("P",  10 ^^   15)
  , ("T",  10 ^^   12)
  , ("G",  10 ^^    9)
  , ("M",  10 ^^    6)
  , ("k",  10 ^^    3)
  , ("h",  10 ^^    2)
  , ("da", 10 ^^    1)
  , ("d",  10 ^^ (- 1))
  , ("c",  10 ^^ (- 2))
  , ("m",  10 ^^ (- 3))
  , ("μ",  10 ^^ (- 6))
  , ("n",  10 ^^ (- 9))
  , ("p",  10 ^^ (-12))
  , ("f",  10 ^^ (-15))
  , ("a",  10 ^^ (-18))
  , ("z",  10 ^^ (-21))
  , ("y",  10 ^^ (-24))
  ]


--------------------------------------------------------------------------------
-- Units
--------------------------------------------------------------------------------

uDimPows ∷ ∀ l m t i th n j x α
         . ( NumType l,  NumType m, NumType t, NumType i
           , NumType th, NumType n, NumType j
           )
         ⇒ Unit (Dim l m t i th n j) α → DimPows
uDimPows _ =
    DimPows (toNum ((⊥) ∷ l))
            (toNum ((⊥) ∷ m))
            (toNum ((⊥) ∷ t))
            (toNum ((⊥) ∷ i))
            (toNum ((⊥) ∷ th))
            (toNum ((⊥) ∷ n))
            (toNum ((⊥) ∷ j))


-- TODO:
-- SI prefixes are not permitted (or never used) together with minute,
-- min; hour, h; day, d. This would solve the ambiguity between cd =
-- candela and cd = centiday.
-- Maybe add a Bool to the tables of units to indicate whether SI
-- prefixes are allowed?

type UnitTable dim α = [(String, Unit dim α)]
type UnitDef   dim α = (UnitTable dim α, UnitTable dim α)

dimensionlessUnits ∷ (Floating α) ⇒ UnitDef DOne α
dimensionlessUnits =
  ( [ ("revolution",  one)
    , ("solid",       one)
    , ("degree",      degree)
    , ("arcminute",   arcminute)
    , ("arcsecond",   arcsecond)
    , ("degreeOfArc", degreeOfArc)
    , ("secondOfArc", secondOfArc)
    , ("minuteOfArc", minuteOfArc)
    ]
  , [ ("°",  degree)
    , ("'",  arcminute)
    , ("\"", arcsecond)
    ]
  )

lengthUnits ∷ (Floating α) ⇒ UnitDef DLength α
lengthUnits =
  ( [ ("metre",        metre)
    , ("meter",        meter)
    , ("foot",         foot)
    , ("inch",         inch)
    , ("yard",         yard)
    , ("mile",         mile)
    , ("nauticalMile", nauticalMile)
    , ("ångström",     metre)
    ]
  , [ ("m", metre)
    , ("Å", prefix (10 ^^ (-10 ∷ Int)) metre)
    ]
  )

massUnits ∷ (Floating α) ⇒ UnitDef DMass α
massUnits =
  ( [ ("gram",       gram)
    , ("poundMass",  poundMass)
    , ("tonne",      tonne)
    , ("metric ton", metricTon)
    ]
  , [ ("g",  gram)
    , ("T",  tonne)
    ]
  )

timeUnits ∷ (Floating α) ⇒ UnitDef DTime α
timeUnits =
  ( [ ("second",  second)
    , ("minute",  minute)
    , ("hour",    hour)
    , ("day",     day)
    , ("year",    year)
    , ("century", century)
    ]
  , [ ("s",   second)
    , ("min", minute)
    , ("h",   hour)
    -- , ("d",   day)
    ]
  )

electricCurrentUnits ∷ (Floating α) ⇒ UnitDef DElectricCurrent α
electricCurrentUnits =
  ( [ ("ampere", ampere)]
  , [ ("A",      ampere)]
  )

thermodynamicTemperatureUnits ∷ (Floating α) ⇒ UnitDef DThermodynamicTemperature α
thermodynamicTemperatureUnits =
  ( [ ("kelvin", kelvin)]
  , [ ("K",      kelvin)]
  )

amountOfSubstanceUnits ∷ (Floating α) ⇒ UnitDef DAmountOfSubstance α
amountOfSubstanceUnits =
  ( [ ("mole", mole)]
  , [ ("mol",  mole)]
  )

luminousIntensityUnits ∷ (Floating α) ⇒ UnitDef DLuminousIntensity α
luminousIntensityUnits =
  ( [ ("candela", candela)]
  , [ ("cd",      candela)]
  )

baseUnitNames   ∷ [(String, DimPows)]
baseUnitSymbols ∷ [(String, DimPows)]
(baseUnitNames, baseUnitSymbols) =
    ( concat [ f (fst dimensionlessUnits)
             , f (fst amountOfSubstanceUnits)
             , f (fst timeUnits)
             , f (fst lengthUnits)
             , f (fst massUnits)
             , f (fst electricCurrentUnits)
             , f (fst thermodynamicTemperatureUnits)
             , f (fst luminousIntensityUnits)
             ]
    , concat [ f (snd dimensionlessUnits)
             , f (snd amountOfSubstanceUnits)
             , f (snd timeUnits)
             , f (snd lengthUnits)
             , f (snd massUnits)
             , f (snd electricCurrentUnits)
             , f (snd thermodynamicTemperatureUnits)
             , f (snd luminousIntensityUnits)
             ]
    )
  where
    f xs = map (Arr.second uDimPows) xs

unsafePUE ∷ String → UnitExp
unsafePUE = either (error ∘ show) id ∘ parseUnitExp

derivedUnitNames ∷ [(String, UnitExp)]
derivedUnitNames =
  [ ("radian",         unsafePUE "metre / metre")
  , ("steradian",      unsafePUE "metre² / metre²")
  , ("hertz",          unsafePUE "second⁻¹")
  , ("newton",         unsafePUE "metre · kilogram · second⁻²")
  , ("pascal",         unsafePUE "metre⁻¹ · kilogram · second⁻²")
  , ("joule",          unsafePUE "metre² · kilogram · second⁻²")
  , ("watt",           unsafePUE "metre² · kilogram · second⁻³")
  , ("coulomb",        unsafePUE "second · ampere")
  , ("volt",           unsafePUE "metre² · kilogram · second⁻³ · ampere⁻¹")
  , ("farad",          unsafePUE "metre⁻² · kilogram⁻¹ · second⁴ · ampere²")
  , ("ohm",            unsafePUE "metre² · kilogram · second⁻³ · ampere⁻²")
  , ("siemens",        unsafePUE "metre⁻² · kilogram⁻¹ · second³ · ampere²")
  , ("weber",          unsafePUE "metre² · kilogram · second⁻² · ampere⁻¹")
  , ("tesla",          unsafePUE "kilogram · second⁻² · ampere⁻¹")
  , ("henry",          unsafePUE "metre² · kilogram · second⁻² · ampere⁻²")
  , ("degree Celsius", unsafePUE "kelvin")
  , ("lumen",          unsafePUE "candela")
  , ("lux",            unsafePUE "metre² · candela")
  , ("becquerel",      unsafePUE "second⁻¹")
  , ("gray",           unsafePUE "metre² · second⁻²")
  , ("sievert",        unsafePUE "metre² · second⁻²")
  , ("katal",          unsafePUE "second⁻¹ · mole")
  ]

derivedUnitSymbols ∷ [(String, UnitExp)]
derivedUnitSymbols =
  [ ( "rad", unsafePUE "m / m")
  , ( "sr",  unsafePUE "m² / m²")
  , ( "Hz",  unsafePUE "s⁻¹")
  , ( "N",   unsafePUE "m · kg · s⁻²")
  , ( "Pa",  unsafePUE "m⁻¹ · kg · s⁻²")
  , ( "J",   unsafePUE "m² · kg · s⁻²")
  , ( "W",   unsafePUE "m² · kg · s⁻³")
  , ( "C",   unsafePUE "s · A")
  , ( "V",   unsafePUE "m² · kg · s⁻³ · A⁻¹")
  , ( "F",   unsafePUE "m⁻² · kg⁻¹ · s⁴ · A²")
  , ( "Ω",   unsafePUE "m² · kg · s⁻³ · A⁻²")
  , ( "S",   unsafePUE "m⁻² · kg⁻¹ · s³ · A²")
  , ( "Wb",  unsafePUE "m² · kg · s⁻² · A⁻¹")
  , ( "T",   unsafePUE "kg · s⁻² · A⁻¹")
  , ( "H",   unsafePUE "m² · kg · s⁻² · A⁻²")
  , ( "℃",   unsafePUE "K")
  , ( "°C",  unsafePUE "K")
  , ( "lm",  unsafePUE "cd")
  , ( "lx",  unsafePUE "m⁻² · cd")
  , ( "Bq",  unsafePUE "s⁻¹")
  , ( "Gy",  unsafePUE "m² · s⁻²")
  , ( "Sv",  unsafePUE "m² · s⁻²")
  , ( "kat", unsafePUE "s⁻¹ · mol")
  ]

-- | Removes all subprefixes and calculates the combined prefix value
-- of the expression.
normalisePrefix ∷ UnitExp → (ℚ, UnitExp)
normalisePrefix n@(UEName _ _) = (1, n)
normalisePrefix (UEPrefix px x) =
    let (p, x') = normalisePrefix x
    in (p ⋅ px, x')
normalisePrefix (UEMul x y) =
    let (px, x') = normalisePrefix x
        (py, y') = normalisePrefix y
    in (px ⋅ py, UEMul x' y')
normalisePrefix (UEDiv x y) =
    let (px, x') = normalisePrefix x
        (py, y') = normalisePrefix y
    in (px / py, UEDiv x' y')
normalisePrefix (UEPow x i) =
    let (px, x') = normalisePrefix x
    in (px ^^ fromIntegral i, UEPow x' i)

-- | Replaces derived units with equivalent expressions using only
-- base SI units.
toBase ∷ UnitExp → UnitExp
toBase ueName@(UEName n _) = maybe ueName id (derivation n)
 where
   derivation ∷ String → Maybe UnitExp
   derivation n = snd <$> find ((n ≡) ∘ fst) (derivedUnitNames ++ derivedUnitSymbols)
toBase (UEPrefix p x) = UEPrefix p (toBase x)
toBase (UEMul x y) = UEMul (toBase x) (toBase y)
toBase (UEDiv x y) = UEDiv (toBase x) (toBase y)
toBase (UEPow x i) = UEPow (toBase x) i

-- | Replaces all divisions with combinations of multiplications and
-- powers. (m/s = m·s⁻¹)
toMulForm ∷ UnitExp → UnitExp
toMulForm n@(UEName _ _) = n
toMulForm (UEPrefix p x) = UEPrefix p (toMulForm x)
toMulForm (UEMul x y) = UEMul (toMulForm x) (toMulForm y)
toMulForm (UEDiv x y) = UEMul (toMulForm x) (UEPow (toMulForm y) (negate 1))
toMulForm (UEPow x i) = UEPow (toMulForm x) i

-- | Extract a list of units and their exponents
-- (m·s⁻¹)² = [m², s⁻²]
extractUnits ∷ UnitExp → Either String [((String, DimPows), ℤ)]
extractUnits ue = filter ((0 ≢) ∘ snd) <$> Map.assocs <$> go ue
  where
    go ∷ UnitExp → Either String (Map (String, DimPows) ℤ)
    go (UEName n d)   = pure $ Map.insert (n, d) 1 Map.empty
    go (UEMul x y)    = Map.unionWith (+) <$> go x <*> go y
    go (UEPow x n)    = Map.map (⋅ n) <$> go x
    go (UEPrefix p x) = throwError "extractUnits: can't deal with prefixes"
    go (UEDiv x y)    = throwError "extractUnits: can't deal with division"

-- Copied from safe-0.3.3 by Neil Mitchell.
readMay ∷ (Read α) ⇒ String → Maybe α
readMay s = case [x | (x,t) ← reads s, ("", "") ← lex t] of
                [x] → Just x
                _   → Nothing

lookupUnit ∷ String → UnitDef dim α → Maybe (Unit dim α)
lookupUnit n (names, symbols) =
    snd <$> (find ((n ≡) ∘ fst) names <|> find ((n ≡) ∘ fst) symbols)

-- | Group units by dimension.
groupUnits ∷ [((String, DimPows), ℤ)] → Map DimPows [(String, ℤ)]
groupUnits = foldr (\((n, d), p) m → Map.insertWith (++) d [(n, p)] m) Map.empty

-- test ∷ ∀ l t α
--      . (NumType l, NumType t, Num α)
--      ⇒ Quantity (Dim l Zero t Zero Zero Zero Zero) α
-- test = 3 *~ (l Dim.* t)
--   where
--     l ∷ Unit (Dim l Zero Zero Zero Zero Zero Zero) α
--     l = (⊥)

--     t ∷ Unit (Dim Zero Zero t Zero Zero Zero Zero) α
--     t = (⊥)

{-
foo ∷ ∀ l m t i th n j α
    . ( NumType l,  NumType m, NumType t, NumType i
      , NumType th, NumType n, NumType j
      , Read α, Num α
      )
    ⇒ String
    → Either String (Quantity (Dim l m t i th n j) α)
foo str = do
    val ← maybe (throwError "Can't parse value") pure $ readMay valStr
    unitExp ← either (Left ∘ show) Right $ parseUnitExp unitStr

    let (p, e) = normalisePrefix $ toMulForm $ toBase unitExp

    unitDimMap ← groupUnits <$> extractUnits e

    let os  = Map.findWithDefault [] (DimPows 0 0 0 0 0 0 0) unitDimMap
        ls  = Map.findWithDefault [] (DimPows 1 0 0 0 0 0 0) unitDimMap
        ms  = Map.findWithDefault [] (DimPows 0 1 0 0 0 0 0) unitDimMap
        ts  = Map.findWithDefault [] (DimPows 0 0 1 0 0 0 0) unitDimMap
        is  = Map.findWithDefault [] (DimPows 0 0 0 1 0 0 0) unitDimMap
        ths = Map.findWithDefault [] (DimPows 0 0 0 0 1 0 0) unitDimMap
        ns  = Map.findWithDefault [] (DimPows 0 0 0 0 0 1 0) unitDimMap
        js  = Map.findWithDefault [] (DimPows 0 0 0 0 0 0 1) unitDimMap

    let os' ∷ (Floating α) ⇒ Maybe [(Unit DOne α, ℤ)]
        os'  = sequence $ map (\(n, x) → (,x) <$> lookupUnit n dimensionlessUnits)            os
        ls'  = sequence $ map (\(n, x) → (,x) <$> lookupUnit n lengthUnits)                   ls
        ms'  = sequence $ map (\(n, x) → (,x) <$> lookupUnit n massUnits)                     ms
        ts'  = sequence $ map (\(n, x) → (,x) <$> lookupUnit n timeUnits)                     ts
        is'  = sequence $ map (\(n, x) → (,x) <$> lookupUnit n electricCurrentUnits)          is
        ths' = sequence $ map (\(n, x) → (,x) <$> lookupUnit n thermodynamicTemperatureUnits) ths
        ns'  = sequence $ map (\(n, x) → (,x) <$> lookupUnit n amountOfSubstanceUnits)        ns

    let test_os = baz unitDimMap dimensionlessUnits

    let oneUnit                      ∷ Unit (Dim Zero Zero Zero Zero Zero Zero Zero) α
        lengthUnit                   ∷ Unit (Dim l    Zero Zero Zero Zero Zero Zero) α
        massUnit                     ∷ Unit (Dim Zero m    Zero Zero Zero Zero Zero) α
        timeUnit                     ∷ Unit (Dim Zero Zero t    Zero Zero Zero Zero) α
        electricCurrentUnit          ∷ Unit (Dim Zero Zero Zero i    Zero Zero Zero) α
        thermodynamicTemperatureUnit ∷ Unit (Dim Zero Zero Zero Zero th   Zero Zero) α
        amountOfSubstanceUnit        ∷ Unit (Dim Zero Zero Zero Zero Zero n    Zero) α
        luminousIntensityUnit        ∷ Unit (Dim Zero Zero Zero Zero Zero Zero j   ) α
        oneUnit                      = (⊥)
        lengthUnit                   = (⊥)
        massUnit                     = (⊥)
        timeUnit                     = (⊥)
        electricCurrentUnit          = (⊥)
        thermodynamicTemperatureUnit = (⊥)
        amountOfSubstanceUnit        = (⊥)
        luminousIntensityUnit        = (⊥)

    return $ val *~ (     oneUnit
                    Dim.* lengthUnit
                    Dim.* massUnit
                    Dim.* timeUnit
                    Dim.* electricCurrentUnit
                    Dim.* thermodynamicTemperatureUnit
                    Dim.* amountOfSubstanceUnit
                    Dim.* luminousIntensityUnit
                    )
  where
    (valStr, unitStr) = Arr.second (dropWhile isSpace) $ break isSpace str

baz ∷ ∀ l m t i th n j α
    . ( NumType l,  NumType m, NumType t, NumType i
      , NumType th, NumType n, NumType j
      )
    ⇒ Map DimPows [(String, ℤ)]
    → UnitDef (Dim l m t i th n j) α
    → Maybe [(Unit (Dim l m t i th n j) α, ℤ)]
baz unitMap unitDef = units
  where
    dimPows ∷ DimPows
    dimPows = uDimPows ((⊥) ∷ Unit (Dim l m t i th n j) α)

    units ∷ Maybe [(Unit (Dim l m t i th n j) α, ℤ)]
    units = sequence
          $ map (\(n, x) → (,x) <$> lookupUnit n unitDef)
          $ Map.findWithDefault [] dimPows unitMap

-}
