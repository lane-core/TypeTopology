\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import Prim.Type
open import Prim.Path

module Properties.Commutative where

is-commutative : {X : 𝓤 ̇} {Y : 𝓥 ̇} (_·_ : X → X → Y) → 𝓤 ⊔ 𝓥 ̇
is-commutative _·_ = ∀ x y → x · y ＝ y · x

\end{code}
