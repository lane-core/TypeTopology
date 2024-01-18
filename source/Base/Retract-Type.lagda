Retracts

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Retract-Type where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Id
open import Base.Notation

get-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (r : X → Y)
           → section-of r
           → (Y → X)
get-section r (s , rs) = s

section-is-inverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (r : X → Y)
                 → (h : section-of r)
                 → r ∘ get-section r h ∼ id
section-is-inverse r (s , rs) = rs

retract_of_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
retract Y of X = Σ r ꞉ (X → Y) , section-of r

data _◁_ (X : 𝓤 ̇) (Y : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 retr : (r₁ : Y → X) (s₁ : X → Y) (rs₁ : r₁ ∘ s₁ ∼ id) → X ◁ Y

retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → (Y → X)
retraction (retr r₁ s₁ rs₁) = r₁

section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → (X → Y)
section (retr r₁ s₁ rs₁) = s₁ 

identity-retraction : {X : 𝓤 ̇ } → X ◁ X
identity-retraction = retr id id (λ x → refl)

◁-refl : (X : 𝓤 ̇ ) → X ◁ X
◁-refl {𝓤} X = identity-retraction {𝓤} {X}

_◀ : (X : 𝓤 ̇ ) → X ◁ X
_◀ = ◁-refl

◁-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                 → Y ◁ X → Z ◁ Y → Z ◁ X
◁-comp (retr r₁ s₁ rs₁) (retr r₂ s₂ rs₂) = retr (r₂ ∘ r₁) (s₁ ∘ s₂) φ
 where
  α : r₂ ∘ r₁ ∘ s₁ ∘ s₂ ∼ r₂ ∘ s₂
  α = ∼-trivial r₂ ◦ rs₁ ◦ ∼-trivial s₂

  φ : r₂ ∘ r₁ ∘ s₁ ∘ s₂ ∼ id
  φ x = α x ∙ rs₂ x

_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
_ ◁⟨ d ⟩ e = ◁-comp e d

instance
 Retr-Comp : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
           → Compose (Y ◁ X) (Z ◁ Y) (λ _ _ → Z ◁ X)
 _◦_ {{Retr-Comp}} = ◁-comp

inverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
        → is-equiv f
        → (Y → X)
inverse f = pr₁ ∘ pr₁

\end{code}

Involution

\begin{code}

\end{code}
