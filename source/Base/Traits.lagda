Elementary notation and instances

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Traits where

open import Base.Type
open import Base.Sigma
open import Base.Id
open import Base.Pi
open import Base.Empty
open import Base.Definitions

record Is-Neutral (X : 𝓤 ̇) (f : X → X) : 𝓤 ̇ where
 field
  neutral : Neutral f

open Is-Neutral {{...}} public

\end{code}

Fixities:

\begin{code}

\end{code}
