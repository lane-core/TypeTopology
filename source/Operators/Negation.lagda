\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import Prim.Type

module Operators.Negation where

record Op-Negation {𝓤} (X : 𝓤 ̇) : 𝓤 ̇ where
 field ¬_ : X → X

\end{code}
