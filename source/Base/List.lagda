Retracts

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.List where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Id
open import Base.Unit
open import Base.Plus
open import Base.Naturals
open import Base.Empty

record List (X : 𝓤 ̇) : 𝓤 ̇ where
 constructor _∷_
 inductive
 field
  x : X
  xs : List X

open List {{...}} public



\end{code}
