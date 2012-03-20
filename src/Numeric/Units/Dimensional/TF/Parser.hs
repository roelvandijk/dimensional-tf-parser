{-# LANGUAGE FlexibleInstances
           , NoImplicitPrelude
           , PackageImports
           , TypeSynonymInstances
           , UnicodeSyntax
  #-}

module Numeric.Units.Dimensional.TF.Parser
  ( PrefixItem
  , UnitItem
  , parse
  , parse'
  , DimUnits, dimUnitNames, dimUnitSymbols
  , polyParse
  , siPrefixNames
  , siPrefixSymbols
  ) where

--------------------------------------------------------------------------------
-- Imports
--------------------------------------------------------------------------------

import "base" Control.Arrow ( (>>>) )
import "base" Data.Bool     ( otherwise, (&&) )
import "base" Data.Char     ( isSpace )
import "base" Data.Either   ( Either(Left, Right) )
import "base" Data.Eq       ( (==) )
import "base" Data.Function ( (.), ($) )
import "base" Data.Int      ( Int )
import "base" Data.List     ( (++), break, concat, drop, dropWhile
                            , find, isPrefixOf, isSuffixOf, length, reverse
                            )
import "base" Data.Maybe    ( Maybe(Nothing, Just) )
import "base" Data.Ord      ( (<) )
import "base" Data.String   ( String )
import "base" Data.Tuple    ( fst )
import "base" Prelude       ( Fractional, Floating, (^^) )
import "base" Text.Read     ( Read, reads, lex )
import "dimensional-tf" Numeric.Units.Dimensional.TF
import "dimensional-tf" Numeric.Units.Dimensional.TF.SIUnits
import "dimensional-tf" Numeric.Units.Dimensional.TF.NonSI


--------------------------------------------------------------------------------
--
--------------------------------------------------------------------------------

type PrefixItem dim α = (String, Unit dim α → Unit dim α)
type UnitItem dim α = (String, Unit dim α)

-- "[PREFIX]UNIT"
parseAtomicUnit ∷ (Fractional α)
                ⇒ [PrefixItem dim α]
                → [UnitItem dim α]
                → String
                → Either (Int, String) (Unit dim α)
parseAtomicUnit prefixes units str =
    case (tryPrefix, tryUnit) of
      (Nothing, Nothing) → Left (length str, "Can't parse: " ++ str)
      (Nothing, Just (us, u))
          | us == str → Right u
          | otherwise → let unknown = dropEnd (length us) str
                        in Left ( length unknown
                                , concat [ "Unknown prefix: "
                                         , unknown
                                         , brackets us
                                         ]
                                )
      (Just (pfs, _), Nothing)
          | pfs == str → Left (0, "Prefix found, unit is missing: " ++ brackets pfs)
          | otherwise  → let unknown = drop (length pfs) str
                         in Left ( length unknown
                                 , concat [ "Prefix found, unknown unit: "
                                          , brackets pfs
                                          , unknown
                                          ]
                                 )
      (Just (pfs, pf), Just (us, u))
          -- Special case when prefix and unit are identical
          -- (consider "m" = milli and "m" = metre).
          | (pfs == str) && (us == str) → Right u
          | pfs ++ us == str → Right $ pf u
          | otherwise → let unknown = dropEnd (length us) (drop (length pfs) str)
                        in Left ( length unknown
                                , concat [ "Can't parse: "
                                         , brackets pfs
                                         , unknown
                                         , brackets us
                                         ]
                                )
  where
    tryPrefix = find (fst >>> (`isPrefixOf` str)) prefixes
    tryUnit   = find (fst >>> (`isSuffixOf` str)) units

parse ∷ (Fractional α, Read α)
      ⇒ [PrefixItem dim α]
      → [UnitItem   dim α]
      → String
      → Either (Int, String) (Quantity dim α)
parse prefixes units str =
    case valMay of
      Nothing → Left (length valStr, "Can't parse value: " ++ valStr)
      Just val →
        case unitEtr of
          Left err → Left err
          Right unit → Right $ val *~ unit
  where (valStr, unitStr') = break isSpace str
        unitStr = dropWhile isSpace unitStr'
        unitEtr = parseAtomicUnit prefixes units unitStr
        valMay = readMay valStr

parse' ∷ (Fractional α, Read α)
       ⇒ [PrefixItem dim α]
       → [PrefixItem dim α]
       → [UnitItem   dim α]
       → [UnitItem   dim α]
       → String
       → Either String (Quantity dim α)
parse' prefixNames prefixSymbols unitNames unitSymbols str =
    case asNames of
      Left (errNameScore, errName) →
           case asSymbols of
             Left (errSymScore, errSym) →
               Left $ if errNameScore < errSymScore
                      then errName
                      else errSym
             Right symbolOk → Right symbolOk
      Right nameOk → Right nameOk
  where
    asNames   = parse prefixNames   unitNames   str
    asSymbols = parse prefixSymbols unitSymbols str

parseSI ∷ (Fractional α, Read α)
        ⇒ [UnitItem dim α]
        → [UnitItem dim α]
        → String
        → Either String (Quantity dim α)
parseSI = parse' siPrefixNames siPrefixSymbols


--------------------------------------------------------------------------------
-- Polymorphic parsing
--------------------------------------------------------------------------------

class DimUnits dim where
    dimUnitNames   ∷ (Floating α) ⇒ [UnitItem dim α]
    dimUnitSymbols ∷ (Floating α) ⇒ [UnitItem dim α]

instance DimUnits DOne where
    dimUnitNames   = [ ("radian",      one)
                     , ("steradian",   one)
                     , ("revolution",  one)
                     , ("solid",       one)
                     , ("degree",      degree)
                     , ("arcminute",   arcminute)
                     , ("arcsecond",   arcsecond)
                     , ("degreeOfArc", degreeOfArc)
                     , ("secondOfArc", secondOfArc)
                     , ("minuteOfArc", minuteOfArc)
                     ]
    dimUnitSymbols = [ ("°",  degree)
                     , ("'",  arcminute)
                     , ("\"", arcsecond)
                     ]

instance DimUnits DLength where
    dimUnitNames   = [ ("metre", metre)
                     , ("meter", metre)
                     , ("foot",  foot)
                     , ("inch",  inch)
                     , ("yard",  yard)
                     , ("mile",  mile)
                     , ("nauticalMile", nauticalMile)
                     , ("ångström", prefix (10 ^^ (-10 ∷ Int)) metre)
                     ]
    dimUnitSymbols = [ ("m", metre)
                     , ("Å", prefix (10 ^^ (-10 ∷ Int)) metre)
                     ]

instance DimUnits DMass where
    dimUnitNames   = [ ("gram",       gram)
                     , ("poundMass",  poundMass)
                     , ("tonne",      tonne)
                     , ("metric ton", metricTon)
                     ]
    dimUnitSymbols = [ ("g",  gram)
                     , ("T",  tonne)
                     ]

instance DimUnits DTime where
    dimUnitNames   = [ ("second",  second)
                     , ("minute",  minute)
                     , ("hour",    hour)
                     , ("day",     day)
                     , ("year",    year)
                     , ("century", century)
                     ]
    dimUnitSymbols = [ ("s",   second)
                     , ("min", minute)
                     , ("h",   hour)
                     , ("d",   day)
                     ]

instance DimUnits DElectricCurrent where
    dimUnitNames   = [ ("ampere", ampere) ]
    dimUnitSymbols = [ ("A",      ampere) ]

instance DimUnits DThermodynamicTemperature where
    dimUnitNames   = [ ("kelvin",         kelvin)
                     , ("degree Celsius", degreeCelsius)
                     ]
    dimUnitSymbols = [ ("K",  kelvin)
                     , ("°C", degreeCelsius)
                     , ("℃",  degreeCelsius)
                     ]

instance DimUnits DAmountOfSubstance where
    dimUnitNames   = [ ("mole", mole) ]
    dimUnitSymbols = [ ("mol",  mole) ]

instance DimUnits DLuminousIntensity where
    dimUnitNames   = [ ("candela", candela) ]
    dimUnitSymbols = [ ("cd",      candela) ]


polyParse ∷ (DimUnits dim, Floating α, Read α) ⇒ String → Either String (Quantity dim α)
polyParse = parseSI dimUnitNames dimUnitSymbols



--------------------------------------------------------------------------------
-- SI prefixes
--------------------------------------------------------------------------------

siPrefixNames ∷ (Fractional α) ⇒ [PrefixItem dim α]
siPrefixNames =
  [ ("yotta", yotta), ("yocto", yocto)
  , ("zetta", zetta), ("zepto", zepto)
  , ("exa"  , exa  ), ("atto" , atto )
  , ("peta" , peta ), ("femto", femto)
  , ("tera" , tera ), ("pico" , pico )
  , ("giga" , giga ), ("nano" , nano )
  , ("mega" , mega ), ("micro", micro)
  , ("kilo" , kilo ), ("milli", milli)
  , ("hecto", hecto), ("centi", centi)
  , ("deca" , deca ), ("deci",  deci)
  , ("deka" , deca )
  ]

siPrefixSymbols ∷ (Fractional α) ⇒ [PrefixItem dim α]
siPrefixSymbols =
  [ ("Y",  yotta), ("y", yocto)
  , ("Z",  zetta), ("z", zepto)
  , ("E",  exa  ), ("a", atto )
  , ("P",  peta ), ("f", femto)
  , ("T",  tera ), ("p", pico )
  , ("G",  giga ), ("n", nano )
  , ("M",  mega ), ("μ", micro)
  , ("k",  kilo ), ("m", milli)
  , ("h",  hecto), ("c", centi)
  , ("da", deca ), ("d", deci )
  ]


--------------------------------------------------------------------------------
-- Utils
--------------------------------------------------------------------------------

-- Copied from safe-0.3.3 by Neil Mitchell.
readMay ∷ (Read α) ⇒ String → Maybe α
readMay s = case [x | (x,t) ← reads s, ("","") ← lex t] of
                [x] → Just x
                _ → Nothing

dropEnd ∷ Int → [α] → [α]
dropEnd n = reverse . drop n . reverse

brackets ∷ String → String
brackets s = "[" ++ s ++ "]"