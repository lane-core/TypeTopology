Empty type

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Empty where

open import Base.Type
open import Base.Unit
open import Base.Operators public

data 𝟘 {𝓤} : 𝓤 ̇ where

𝟘-induction : {A : 𝟘 {𝓤} → 𝓥 ̇ } → (x : 𝟘) → A x
𝟘-induction = λ ()

unique-from-𝟘 : {A : 𝓥 ̇ } → 𝟘 {𝓤} → A
unique-from-𝟘 = 𝟘-induction

𝟘-elim = unique-from-𝟘

Not_ : 𝓤 ̇ → 𝓤 ̇
Not_ {𝓤} X = X → 𝟘 {𝓤₀}

instance
 ¬-Empty : Negation (𝓤 ̇) Uni
 ¬-Empty = record { ¬_ = Not_ }

¬¬_ ¬¬¬_ : 𝓤 ̇ → 𝓤 ̇
¬¬  A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)

-- a version of empty which 'computes' by vacuous induction
record Empty {𝓤 : Universe} : 𝓤 ̇ where
 inductive
 constructor ⊢
 pattern
 field
  ∅ : Empty {𝓤}

open Empty public

Empty-induction : (A : Empty {𝓤} → 𝓥 ̇) → (∅ : Empty) → A ∅
Empty-induction A (⊢ ∅) = Empty-induction (λ x → A (⊢ ∅)) ∅

¬Empty : ¬ Empty {𝓤}
¬Empty ∅ = Empty-induction (λ _ → 𝟘) ∅

\end{code}
