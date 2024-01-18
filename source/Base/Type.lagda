\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Type where

open import Agda.Primitive public
 renaming ( lzero to 𝓤₀
          ; lsuc to _⁺
          ; Level to Universe
          ; Set to Type
          ; Setω to 𝓤ω
          )

variable
  𝓤 𝓥 𝓦 𝓣 𝓤' 𝓥' 𝓦' 𝓣' : Universe

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

_̇ : (𝓤 : Universe) → Type (𝓤 ⁺)
𝓤 ̇ = Type 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺

domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

object : {X : 𝓤 ̇ } → X → 𝓤 ̇
object {𝓤} {X} x = X

Uni : 𝓤 ̇ → 𝓤 ⁺ ̇
Uni {𝓤} X = 𝓤 ̇

maps-to : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → ((x : X) → Y x) → (x : X) → Y x
maps-to f = f

syntax maps-to (λ x → b) = x ↦ b

Maps-to : (X : 𝓤 ̇ ) {Y : X → 𝓥 ̇ } → ((x : X) → Y x) → (x : X) → Y x
Maps-to X f = f

syntax Maps-to A (λ x → b) = x ꞉ A ↦ b

Predicate : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (x : X) → 𝓥  ̇
Predicate {𝓤} {𝓥} A x = A x

_⊢_ : {X : 𝓤 ̇} (x : X) (A : X → 𝓥 ̇) → 𝓥  ̇
a ⊢ A = Predicate A a

{-# DISPLAY Predicate A x = x ⊢ A #-}

Predicate₂ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} (A : (x : X) → Y x → 𝓦 ̇) → (x : X) (y : Y x) → 𝓦 ̇
Predicate₂ A x y = A x y

_,_⊢_ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} (x : X) (y : Y x) (A : (x : X) → Y x → 𝓦 ̇) → 𝓦 ̇
x , y ⊢ A = Predicate₂ A x y

{-# DISPLAY Predicate₂ A x y = x , y ⊢ A #-}

id : {X : 𝓤 ̇} → X → X
id x = x

unit : (X : 𝓤 ̇ ) → X → X
unit X = id

𝒦 : {X : 𝓤 ̇} {Y : 𝓥 ̇} (x : X) → Y → X
𝒦 x = λ _ → x -- K-combinator

𝒮 : {X : 𝓤 ̇} {Y : X → 𝓥 ̇ } {Z : (x : X) → Y x → 𝓦 ̇ }
             → ((x : X) (y : Y x) → Z x y)
             → (f : (x : X) → Y x) (x : X) → Z x (f x)
𝒮 g f = λ x → g x (f x) -- S-combinator

{-# INLINE 𝒮 #-}

\end{code}

Fixities

\begin{code}

infix 1 _̇
infixl -1 𝟏
infixr 10 maps-to
infixr 10 Maps-to

\end{code}
