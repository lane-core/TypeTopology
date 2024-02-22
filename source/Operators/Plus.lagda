\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import Prim.Type

module Operators.Plus where

record `+` {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇) (Y : 𝓥 ̇) (Z : 𝓦 ̇) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ where
 field _+_ : X → Y → Z
 add = _+_

open `+` {{...}} public

{-# DISPLAY `+`._+_ _ _ _ a b  = a + b #-}

\end{code}
