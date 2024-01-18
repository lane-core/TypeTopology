Retracts

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Retracts where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Id
open import Base.Homotopy
open import Base.Operators
open import Base.Definitions
open import Base.Equiv

get-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (r : X → Y)
           → Section r
           → (Y → X)
get-section r (s , rs) = s

section-is-inverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (r : X → Y)
                 → (h : Section r)
                 → r ∘ get-section r h ∼ id
section-is-inverse r (s , rs) = rs

retract_of_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
retract Y of X = Σ r ꞉ (X → Y) , Section r

_◁_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
Y ◁ X = Σ r ꞉ (X → Y) , Section r

retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → (Y → X)
retraction (r , s , rs) = r

section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → (X → Y)
section (r , s , rs) = s

identity-retraction : {X : 𝓤 ̇ } → X ◁ X
identity-retraction = id , id , λ x → refl

◁-refl : (X : 𝓤 ̇ ) → X ◁ X
◁-refl {𝓤} X = identity-retraction {𝓤} {X}

_◀ : (X : 𝓤 ̇ ) → X ◁ X
_◀ = ◁-refl

◁-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                 → Y ◁ X → Z ◁ Y → Z ◁ X
◁-comp (r , s , rs) (r' , s' , rs') =
  r' ∘ r , s ∘ s' , λ z → r' (r (s (s' z))) ＝⟨ ap r' (rs (s' z)) ⟩
                          r' (s' z)         ＝⟨ rs' z ⟩
                          z                 ∎

_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
_ ◁⟨ d ⟩ e = ◁-comp e d

instance
 Retr-Comp : {X : 𝓤 ̇} {Y : 𝓥 ̇}
           → Compose (Σ f ꞉ (Y → Y) , Σ g ꞉ (Y → Y) , ((y : Y) → f (g y) ＝ y))
           (λ _ → Σ f ꞉ (Y → Y) , Σ g ꞉ (Y → Y) , ((y : Y) → f (g y) ＝ y))
           λ _ _ → Σ f ꞉ (Y → Y) , Σ g ꞉ (Y → Y) , ((x : Y) → f (g x) ＝ x)
 _◦_ {{Retr-Comp}} = ◁-comp

inverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
        → is-equiv f
        → (Y → X)
inverse f = pr₁ ∘ pr₁

-- inverse-id : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → (e : Equiv f) → (inverse f e) ∘ f ∼ id
-- inverse-id f ((s , id₁) , r , id₂) =
--  x ↦ (s (f x) ＝⟨ {!!} ⟩
--       {!f (s (f x))!} ＝⟨ {!!} ⟩
--       {!!} ＝⟨ {!!} ⟩
--           x ∎)

\end{code}
