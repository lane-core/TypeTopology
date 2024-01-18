Martin Escardo

In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

\begin{code}

{-# OPTIONS --safe --without-K --prop #-}

module Base.Prop where

open import Base.Type
open import Base.Subsingletons
open import Base.Pi
open import Base.Sigma
open import Base.Plus
open import Base.Id
open import Base.Empty

𝓟 : (𝓤 : Universe)  → 𝓤 ⁺ ̇
𝓟 𝓤 = Σ X ꞉ (𝓤 ̇), is-prop X

⋆id : {X : ⟦ 𝓤 ⟧} → X → X
⋆id x = x

data _≐_ {X : ⟦ 𝓤 ⟧} (x : X) : X → ⟦ 𝓤 ⟧ where
 instance refl : x ≐ x

data ∥_∥ (X : 𝓤 ̇) : ⟦ 𝓤 ⟧ where
 ∣_∣ : X → ∥ X ∥

∥∥-induction : {X : 𝓤 ̇} {P : ∥ X ∥ → ⟦ 𝓥 ⟧}
            → ((s : ∥ X ∥) → P s)
            → ((x : X) → P ∣ x ∣)
            → (s : ∥ X ∥) → P s
∥∥-induction f g s = f s

∥∥-rec : {X : 𝓤 ̇ } (P : ⟦ 𝓥 ⟧) → (X → P) → ∥ X ∥ → P
∥∥-rec P f ∣ x ∣ = ∥∥-induction (λ _ → f x) f ∣ x ∣

∥∥-recursion-computation : {X : 𝓤 ̇ } (P :  ⟦ 𝓥 ⟧ )
                           → (f : X → P)
                           → (x : X)
                           → ∥∥-rec P f ∣ x ∣ ≐ f x
∥∥-recursion-computation P f x = refl

∥∥-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → ∥ X ∥ → ∥ Y ∥
∥∥-functor {𝓤} {𝓥} {X} {Y} f = ∥∥-rec ∥ Y ∥ (λ x → ∣ f x ∣)

record 𝚺 {X : 𝓤 ̇} (Y : ∥ X ∥ → ⟦ 𝓥 ⟧) : ⟦ 𝓤 ⊔ 𝓥 ⟧ where
 constructor _,_
 field
  pr₁ : ∥ X ∥
  pr₂ : Y pr₁

⋆Sigma : (X : 𝓤 ̇) (Y : ∥ X ∥ → ⟦ 𝓥 ⟧) → ⟦ 𝓤 ⊔ 𝓥 ⟧
⋆Sigma X Y = 𝚺 Y

Ω : 𝓤 ̇ → ⟦ 𝓤 ⟧
Ω X = ⋆Sigma X (λ _ → ∥ is-prop X ∥)

prop-id-embedding : {X : 𝓤 ̇} (x y : X) → ∥ is-prop X ∥ → ∥ x ＝ y ∥
prop-id-embedding x y ∣ p ∣ = ∣ p x y ∣

hmm : {P Q : ⟦ 𝓤 ⟧} → (P → Q) → (Q → P) → P ＝ Q
hmm p q = {!!}

data ⊥ {𝓤} : ⟦ 𝓤 ⟧ where

⊥-type-induction : {A : ⊥ {𝓤} → 𝓥 ̇} → (x : ⊥) → A x
⊥-type-induction = λ ()

⊥-prop-induction : {A : ⊥ {𝓤} → ⟦ 𝓥 ⟧} → (x : ⊥) → A x
⊥-prop-induction = λ ()

record ⊤ : ⟦ 𝓤 ⟧ where constructor ⋆

open ⊤ public

⟦⟧-transport : {X : ⟦ 𝓤 ⟧} {A : X → ⟦ 𝓥 ⟧}  → {a b : X} → a ≐ b → A a → A b
⟦⟧-transport p = ⋆id



_∧_ : 𝓤 ̇ → 𝓥 ̇ → ⟦ 𝓤 ⊔ 𝓥 ⟧
P ∧ Q = ∥ P × Q ∥

_∨_ : 𝓤 ̇ → 𝓥 ̇ → ⟦ 𝓤 ⊔ 𝓥 ⟧
P ∨ Q = ∥ P + Q ∥

∥∥-cases : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : ⟦ 𝓦 ⟧} → (X → A) → (Y → A) → X + Y → A
∥∥-cases f g (inl x) = f x
∥∥-cases f g (inr x) = g x

∃ : {X : 𝓤 ̇} (Y : X → 𝓥 ̇) → ⟦ 𝓤 ⊔ 𝓥 ⟧
∃ Y = ∥ Σ Y ∥

~_ : ⟦ 𝓤 ⟧ → ⟦ 𝓤 ⟧
~ P = P → ⊥ {𝓤₀}

Exists : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → ⟦ 𝓤 ⊔ 𝓥 ⟧
Exists X Y = ∃ Y

syntax Exists A (λ x → b) = ∃ x ꞉ A , b
infixr -1 Exists

∨-elim : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } (R : ⟦ 𝓦 ⟧)
       → (P → R)
       → (Q → R)
       → P ∨ Q → R
∨-elim i f g = ∥∥-rec i (∥∥-cases f g)

inhabited-is-nonempty : {X : 𝓤 ̇ } → X → ~ (~ ∥ X ∥)
inhabited-is-nonempty x = λ p → p ∣ x ∣

value : (X : 𝓤 ̇) (x : X) → ∥ x ＝ x ∥
value X x = ∣ refl ∣

test : (x y : X) (p q : ∥ x ＝ y ∥) → p ≐ q
test = λ x y p q → refl

-- data □ (A : ⟦ 𝓤 ⟧) : 𝓤 ̇ where
--  box : A → □ A

-- prop-gives-Prop : {P : 𝓤 ̇} → ∥ is-prop P ∥ → ∥ P ∥
-- prop-gives-Prop {𝓤} {P} = {!!} --∥∥-functor φ
--  where
--   φ : {x : P} → is-prop P → P
--   φ {x} = {!!}


Empty-is-prop : is-prop (Empty {𝓤})
Empty-is-prop = Empty-induction (λ u → (x : Empty) → u ＝ x)


Unit-is-prop : is-prop (Unit 𝓤)
Unit-is-prop p q = ap (Empty-induction λ e → {!!}) refl


\end{code}
