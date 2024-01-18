-- Identity type

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Image where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Unit
open import Base.Empty
open import Base.Nat
open import Base.Operators public
open import Base.Equiv

data _◂_⟶_ {X : 𝓤 ̇} {Y : X → 𝓥 ̇} (f : (x : X) → Y x) (x : X) : (Y x) → 𝓤 ⊔ 𝓥  ̇ where
 app : f ◂ x ⟶ f x

morphism : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {f : (x : X) → Y x} {x : X} {y : Y x}
       → f ◂ x ⟶ y → (x : X) → Y x
morphism {𝓤} {𝓥} {X} {Y} {f} p = f

source : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {f : (x : X) → Y x} {x : X} {y : Y x}
       → f ◂ x ⟶ y → X
source {𝓤} {𝓥} {X} {Y} {f} {x} p = x

target : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {f : (x : X) → Y x} {x : X} {y : Y x}
       → f ◂ x ⟶ y → Y x
target {𝓤} {𝓥} {X} {Y} {f} {x} {y} p = y

ap : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} {f : X → Y} {x : X} {y : Y}
   (g : Y → Z) → f ◂ x ⟶ y → (g ∘ f) ◂ x ⟶ g y
ap g app = app

App-to-Σ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {x : X} {y : Y x} {f : ∀ x → Y x}
         → f ◂ x ⟶ y → Σ Y
App-to-Σ p = source p , target p

App-to-Π : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {x : X} {y : Y x} {f : ∀ x → Y x}
         → f ◂ x ⟶ y → Π Y
App-to-Π p = morphism p

Ibased : {X : 𝓤 ̇} (x : X) {Y : X → 𝓥 ̇} {f : ∀ x → Y x}
  → (A : ∀ y → f ◂ x ⟶ y → 𝓦 ̇) → A (f x) app
  → (y : Y x) (r : f ◂ x ⟶ y) → A y r
Ibased x {Y} {f} A b .(f x) app = b

𝕀 : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {f : ∀ x → Y x}
  → (A : ∀ x y → f ◂ x ⟶ y → 𝓦 ̇) → (∀ x → A x (f x) app)
  → {x : X} {y : Y x} → (r : f ◂ x ⟶ y) → A x y r
𝕀 A f {x} app = f x

transport-app : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} (A : ∀ {x} → Y x → 𝓦 ̇) {f : ∀ x → Y x}
               {x : X} {y : Y x} → f ◂ x ⟶ y → A (f x) → A y
transport-app A app = id

Id : (X : 𝓤 ̇) → X → X → 𝓤 ̇
Id X x y = id ◂ x ⟶ y

_≡_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
_≡_ {𝓤} {X} = Id X

refl : {X : 𝓤 ̇} {x : X} → x ≡ x
refl = app

sym' : {X : 𝓤 ̇} {x y : X} → x ≡ y → y ≡ x
sym' app = app

trans' : {X : 𝓤 ̇} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
trans' app app = app

ap≡ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) {x y : X} → x ≡ y → f x ≡ f y
ap≡ f app = ap id app

transport' : {X : 𝓤 ̇} (A : X → 𝓥 ̇) {x y : X} → x ≡ y → A x → A y
transport' A = transport-app A

Hom : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Hom X Y = (f : Π Y) → ∀ y → Σ x ꞉ f ◂ x ⟶ y

app-to-id : {X : 𝓤 ̇} {x y : X} → id ◂ x ⟶ y → x ≡ y
app-to-id = id

id-to-app : {X : 𝓤 ̇} {x y : X} → x ≡ y → id ◂ x ⟶ y
id-to-app = id

is-prop' : (X : 𝓤 ̇) → 𝓤 ̇
is-prop' X = (x y : X) (p q : x ≡ y) → p ≡ q

fiber : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
fiber f y = Σ x ꞉ domain f , f ◂ x ⟶ y

each-fiber-of : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → (X → Y)
              → (𝓤 ⊔ 𝓥 ̇ → 𝓦 ̇)
              → 𝓥 ⊔ 𝓦 ̇
each-fiber-of f P = ∀ y → P (fiber f y)

is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-embedding f = each-fiber-of f is-prop'

\end{code}

Infixities

\begin{code}
\end{code}
