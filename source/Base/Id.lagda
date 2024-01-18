-- Identity type

\begin{code}
{-# OPTIONS --safe --without-K #-}

module Base.Id where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Unit
open import Base.Empty
open import Base.Operators public

private variable
 X : 𝓤 ̇

data _＝_ {𝓤} {X : 𝓤 ̇} : X → X → 𝓤 ̇ where
  instance refl : {x : X} → x ＝ x

{-# BUILTIN EQUALITY _＝_ #-}

Id : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
Id = _＝_

-Id : (X : 𝓤 ̇ ) → X → X → 𝓤 ̇
-Id X x y = x ＝ y

syntax -Id X x y = x ＝[ X ] y

id-is-𝒦 : {X : 𝓤 ̇} {Y : 𝓥 ̇} → unit X ＝ λ x → 𝒦 x Y
id-is-𝒦 = refl

\end{code}

J and Transport

\begin{code}

Jbased : {X : 𝓤 ̇ } (x : X) (A : (y : X) → x ＝ y → 𝓥 ̇ )
       → A x refl → (y : X) (r : x ＝ y) → A y r
Jbased x A b .x refl = b

𝕁 : {X : 𝓤 ̇ } (A : (x y : X) → x ＝ y → 𝓥 ̇ )
  → ((x : X) → A x x refl) → {x y : X} (r : x ＝ y) → A x y r
𝕁 A f {x} {y} = Jbased x (A x) (f x) y

transport : (A : X → 𝓥 ̇) {x y : X} → x ＝ y → A x → A y
transport A refl = id

transport₂ : {Y : 𝓥 ̇} (A : X → Y → 𝓦 ̇)
             {x x' : X} {y y' : Y}
           → x ＝ x' → y ＝ y' → A x y → A x' y'
transport₂ A refl refl = id

_↝_ : {X : 𝓤 ̇}{x y : X} → x ＝ y → (A : X → 𝓥 ̇) → A x → A y
p ↝ A = transport A p

_↝₂_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {x x' : X} {y y' : Y}
     → (x ＝ x') × (y ＝ y')
     → (A : X → Y → 𝓦 ̇)
     → A x y → A x' y'
(p , q) ↝₂ A = transport₂ A p q

--syntax transport A p = p ↝ A

lhs : {X : 𝓤 ̇ } {x y : X} → x ＝ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ＝ y → X
rhs {𝓤} {X} {x} {y} p = y

ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ＝ x' → f x ＝ f x'
ap f p = (p ↝ (λ - → f (lhs p) ＝ f -)) refl

instance
 Ap-Comp : {X : 𝓤 ̇} {Y : 𝓥 ̇} {x x' : X}
         → Compose (X → Y) (λ _ → x ＝ x') (λ f _ → f x ＝ f x')
 _∘_ {{Ap-Comp}} f p = ap f p

ap₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x₀ x₁ : X} {y₀ y₁ : Y}
    → x₀ ＝ x₁
    → y₀ ＝ y₁
    → f x₀ y₀ ＝ f x₁ y₁
ap₂ f refl refl = refl

\end{code}

Order properties

\begin{code}

explicit-refl : {X : 𝓤 ̇ } (x : X) → x ＝ x
explicit-refl x = refl {_} {_} {x}

instance
 Id-erefl : {X : 𝓤 ̇} → Identity X (λ x → x ＝ x)
 Id-erefl = record { ℯ = refl ; ℰ = explicit-refl }

sym : {X : 𝓤 ̇} {x y : X} → x ＝ y → y ＝ x
sym p = (p ↝ x ↦ (x ＝ lhs p)) refl

instance
 Id-Inv : {X : 𝓤 ̇} {x y : X} → Inverse (x ＝ y) (λ _ → y ＝ x)
 _⁻¹ {{Id-Inv}} = sym

transport⁻¹ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} → x ＝ y → A y → A x
transport⁻¹ B p = transport B (p ⁻¹)

_↜_ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} → x ＝ y → A y → A x
A ↜ p = transport⁻¹ A p

trans : {X : 𝓤 ̇ } {x y z : X} → x ＝ y → y ＝ z → x ＝ z
trans p q = (q ↝ λ x → lhs p ＝ x) p

instance
 Id-Dot : {X : 𝓤 ̇} {x y z : X} → Dot (x ＝ y) (y ＝ z) (x ＝ z)
 _∙_ {{Id-Dot}} = trans

sym-involutive : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → (p ⁻¹) ⁻¹ ＝ p
sym-involutive refl = refl

\end{code}

Standard syntax for equality chain reasoning:

\begin{code}

_＝⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ＝ y → y ＝ z → x ＝ z
_ ＝⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇ } (x : X) → x ＝ x
_∎ _ = refl

\end{code}

Non-equality

\begin{code}

_≠_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≠ y = ¬ (x ＝ y)

≠-sym : {X : 𝓤 ̇ } → {x y : X} → x ≠ y → y ≠ x
≠-sym u r = u (sym r)

\end{code}

Trait definitions

\begin{code}

{-# DISPLAY trans p q = p ∙ q #-}

\end{code}

Infixities

\begin{code}

infixr 2 transport
infixr -1 transport₂
infix  0 _＝_
infixl 8 _↝_
infix  3 sym
infix  1 _∎
infixr 0 _＝⟨_⟩_

\end{code}
