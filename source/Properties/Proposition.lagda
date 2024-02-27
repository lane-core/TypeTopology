\begin{code}

{-# OPTIONS --safe --without-K #-}

module Properties.Proposition where

open import Prim.Prelude
open import Properties.Contractible

is-prop : End (𝓤 ̇)
is-prop X = Π x ꞉ X , Π y ꞉ X , x ＝ y

record Ω (X : 𝓤 ̇) : 𝓤 ̇ where
 field
  prop : is-prop X

 is-truth-value is-subsingleton : 𝓤 ̇ → 𝓤 ̇
 is-truth-value  = Ω
 is-subsingleton = Ω

open Ω public



-- 𝟙-is-prop : is-prop (𝟙 {𝓤})
-- 𝟙-is-prop {𝓤} ⋆ ⋆ = path , (λ (x : Hom ⋆ ⋆) → {!!})
--  where

\end{code}
