\begin{code}

{-# OPTIONS --safe --without-K #-}

module Prim.Id where

open import Prim.Type

data _≡_ {X : 𝓤 ̇} : X → X → 𝓤  ̇ where
 rfl : {x : X} → x ≡ x

\end{code}

Infixities

\begin{code}

--infixr 2 trans
--infixr 3 sym
infixl 0 _≡_

\end{code}
