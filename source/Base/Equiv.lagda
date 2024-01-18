Equivalence

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Equiv where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Id
open import Base.Homotopy

Section : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
Section r = Σ s ꞉ (codomain r → domain r), r ∘ s ∼ id

Retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
Retraction s = Σ r ꞉ (codomain s → domain s), r ∘ s ∼ id

is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-equiv f = Section f × Retraction f

_≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ≃ Y = Σ f ꞉ (X → Y) , is-equiv f

Aut : 𝓤 ̇ → 𝓤 ̇
Aut X = (X ≃ X)

id-is-equiv : (X : 𝓤 ̇ ) → is-equiv (id {𝓤} {X})
id-is-equiv X = (id , λ x → refl) , (id , λ x → refl)

≃-refl : (X : 𝓤 ̇ ) → X ≃ X
≃-refl X = id , id-is-equiv X

𝕚𝕕 : {X : 𝓤 ̇ } → X ≃ X
𝕚𝕕 = ≃-refl _

\end{code}

Prove some properties of the identity type

\begin{code}

sym-is-equivalent : {X : 𝓤 ̇} {x y : X} → (x ＝ y) ≃ (y ＝ x)
sym-is-equivalent = sym , (sym , λ p → sym-involutive p) , sym , λ p → sym-involutive p

\end{code}



\begin{code}



\end{code}

\begin{code}

\end{code}

 -- ⁻¹-is-equiv {{Id-Inv}} = ?
 -- involutive {{Id-Inv}} = ?
