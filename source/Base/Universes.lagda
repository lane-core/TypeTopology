\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Universes where

open import Base.Type
open import Base.Sigma
open import Base.Retracts
open import Base.Naturals
open import Base.Notation
open import Base.Traits
open import Base.Pi
open import Base.Id
open import Base.Unit

neighborhood : 𝓤 ̇ → Universe
neighborhood {𝓤} X = 𝓤

-- 1lab
_•̇ : (𝓤 : Universe) → 𝓤 ⁺ ̇
𝓤 •̇ = Σ X ꞉ (𝓤 ̇) , X

_→̇_ : 𝓤 •̇ → 𝓥 •̇ → 𝓤 ⊔ 𝓥 ̇
(A , a) →̇ (B , b) = Σ f ꞉ (A → B) , f a ＝ b


universe-of : (X : 𝓤 ̇) → 𝓤 ⁺ ̇
universe-of {𝓤} x = 𝓤 ̇

test : Universe → Universe
test = ?

_∈_ : (u v : Universe)  → (u ⁺⁺) ⊔ v ⁺ ̇
u ∈ v = (u ⁺ ̇) ◁ (v ̇) 

trivial-∼ : {X : 𝓤 ̇} → 𝒦 id X ∼ 𝒦 id X
trivial-∼ = λ x → refl

∈-belonging : 𝓤 ∈ (𝓤 ⁺)
∈-belonging = id , id , λ x → refl

∈-trans : {u v w : Universe} → u ∈ v → v ∈ w → u ∈ w
∈-trans (s₁ , r₁ , id₁) (s₂ , r₂ , id₂) = {!r₂!} , ({!!} , {!!})

-- ∈-trans : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X ∈ 𝓥 → Y ∈ 𝓦 → X ∈ 𝓦
-- ∈-trans {𝓤} {𝓥} {𝓦} {X} {Y} (s₁ , r₁ , rs₁) (s₂ , r₂ , rs₂) = {!!} , ({!!} , {!!})
--  where
  -- φ : (X : 𝓤 ̇) → s₁ (s₂ (r₂ (r₁ X))) ＝ X
  -- φ X = transport (λ u → s₁ u ＝ X) (rs₂ (r₁ X) ⁻¹) (rs₁ X)

-- powerset-structure₀ : (𝓥 : Universe) (P : 𝓥 ̇ → 𝓥 ̇) → 𝓥 ̇
-- powerset-structure₀ 𝓥 = {a b c : 𝓥 ̇} → a ∈ (P c) → (a ∈ 𝓥) →

-- ∈-belonging⁺ : {X : 𝓤 ̇} → X ∈ (𝓤 ⁺)
-- ∈-belonging⁺ {𝓤} {X} = {!!} , {!!}


--gr-transitive : {u : 𝓤 ⁺ ̇} {t : 𝓤 ̇} → t



\end{code}
