\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import Prim.Type

module Operators.Inverse where

record Op-Inverse (X Y : 𝓤 ̇) : 𝓤  ̇ where
 field _⁻¹ : X → Y

\end{code}
