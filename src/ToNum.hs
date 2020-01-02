{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE UnicodeSyntax     #-}

module ToNum
  ( ToNum( toNum, toNumI, toNumi, toNumN, toNumℕ
         , toNumW8, toNumW16, toNumW32, toNumW64 ) )
where

import Prelude  ( Int, Integer, Num )

-- base --------------------------------

import Data.Word      ( Word8, Word16, Word32, Word64 )

-- more-unicode ------------------------

import Data.MoreUnicode.Natural  ( ℕ )

--------------------------------------------------------------------------------

class ToNum α where
  toNum   ∷ Num β ⇒ α → β
  toNumI  ∷ α → Integer
  toNumI  = toNum
  toNumi  ∷ α → Int
  toNumi  = toNum
  toNumN  ∷ α → ℕ
  toNumN  = toNum
  toNumℕ  ∷ α → ℕ
  toNumℕ  = toNum
  toNumW8  ∷ α → Word8
  toNumW8  = toNum
  toNumW16 ∷ α → Word16
  toNumW16 = toNum
  toNumW32 ∷ α → Word32
  toNumW32 = toNum
  toNumW64 ∷ α → Word64
  toNumW64 = toNum

-- that's all, folks! ----------------------------------------------------------
