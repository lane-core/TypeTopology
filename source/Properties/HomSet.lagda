\begin{code}

{-# OPTIONS --safe --without-K #-}

module Properties.HomSet where

open import Prim.Type
open import Prim.Path
open import Prim.Pi
open import Prim.Sigma
open import Properties.Proposition

is-hom : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → 𝓤 ⊔ 𝓥 ̇
is-hom f = Π x ꞉ domain f , Σ y ꞉ codomain f , is-prop (f x ＝ y)

hom-set : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
hom-set X Y = Σ f ꞉ (X → Y) , is-hom f

\end{code}
