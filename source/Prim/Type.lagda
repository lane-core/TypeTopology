\begin{code}

{-# OPTIONS --safe --without-K #-}

module Prim.Type where

open import Agda.Primitive public
 renaming ( lzero to 𝓤₀
          ; lsuc to _⁺
          ; Level to Universe
          ; Set to Obj
          ; Setω to 𝓤ω
          )
 hiding (Prop)

variable
 𝓤 𝓥 𝓦 𝓣 𝓒 𝓓 𝓤' 𝓥' 𝓦' 𝓣' 𝓒' 𝓓'  : Universe

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

_̇ : (𝓤 : Universe) → Obj (𝓤 ⁺)
𝓤 ̇ = Obj 𝓤

Type : 𝓤 ⁺ ̇
Type {𝓤} = 𝓤 ̇

record Lift {𝓤 𝓥} (X : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 constructor lift
 field lower : X

\end{code}

Fixities

\begin{code}

infix 1 _̇

\end{code}
