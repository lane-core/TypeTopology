Nat type

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Nat where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Id
open import Base.Homotopy
open import Base.Operators

Nat : {X : 𝓤 ̇} → (X → 𝓥 ̇) → (X → 𝓦 ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
Nat A B = ∀ x → A x → B x

syntax Nat A B = ▰ A ↦ B

-- instance
--  Nat-functor : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇} {τ : Nat A B}
--              → Functor ({!τ ?!})
--  Nat-functor {𝓤} {𝓥} {𝓦} {X} {A} {B} {τ} = record { fmap = {!!} ; fmap-id = {!!} ; fmap-comp = {!!} }
--   where

Nat-trans : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇} {C : X → 𝓣 ̇}
          → ▰ A ↦ B → ▰ B ↦ C → ▰ A ↦ C
Nat-trans f g = λ x z → g x (f x z)

{-# INLINE Nat-trans #-}

instance
 Nat-Comp : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇} {C : X → 𝓣 ̇}
          → Compose (Nat A B) (λ _ → Nat B C) (λ _ _ → Nat A C)
 _∘_ {{Nat-Comp}} f g = Nat-trans f g

Nats-are-natural : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
                   (τ : Nat A B) {x y : X} (p : x ＝ y)
                 → τ y ∘ transport A p ＝ transport B p ∘ τ x
Nats-are-natural A B τ refl = refl

Nats-are-natural-∼ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
                     (τ : Nat A B) {x y : X} (p : x ＝ y)
                   → τ y ∘ (p ↝ A) ∼ (p ↝ B) ∘ τ x
Nats-are-natural-∼ A B τ refl a = refl

NatΣ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → Σ A → Σ B
NatΣ ζ (x , a) = (x , ζ x a)

NatΠ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → ▰ A ↦ B → Π A → Π B
NatΠ f g x = f x (g x) -- (S combinator from combinatory logic!)

ΠΣ-distr : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
         → (Π x ꞉ X , Σ a ꞉ A x , P x a)
         → Σ f ꞉ Π A , Π x ꞉ X , P x (f x)
ΠΣ-distr φ = (λ x → pr₁ (φ x)) , λ x → pr₂ (φ x)

ΠΣ-distr⁻¹ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
           → (Σ f ꞉ Π A , Π x ꞉ X , P x (f x))
           → Π x ꞉ X , Σ a ꞉ A x , P x a
ΠΣ-distr⁻¹ (f , φ) x = f x , φ x

_≈_ : {X : 𝓤 ̇ } {x : X} {A : X → 𝓥 ̇ } → ▰ (Id x) ↦ A → ▰ (Id x) ↦ A → 𝓤 ⊔ 𝓥 ̇
η ≈ θ = ∀ y → η y ∼ θ y

\end{code}

Yoneda

\begin{code}

𝓨 : {X : 𝓤 ̇ } → X → (X → 𝓤 ̇ )
𝓨 {𝓤} {X} = -Id X

𝑌 : (X : 𝓤 ̇ ) → X → (X → 𝓤 ̇ )
𝑌 {𝓤} X = 𝓨 {𝓤} {X}

transport-lemma : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
                → (τ : Nat (𝓨 x) A)
                → (y : X) (p : x ＝ y) → τ y p ＝ transport A p (τ x refl)

transport-lemma A x τ x refl = refl {_} {_} {τ x refl}

𝓔 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X) → ▰ (𝓨 x) ↦ A → A x
𝓔 A x τ = τ x refl

𝓝 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X) → A x → ▰ (𝓨 x) ↦ A
𝓝 A x a y p = transport A p a

\end{code}
