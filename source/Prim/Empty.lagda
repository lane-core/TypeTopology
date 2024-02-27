Empty type citing MLTT.Empty and UF.Subsingletons

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Prim.Empty where

open import Prim.Type
open import Prim.Sigma
open import Prim.Path
--open import Prim.Prop
open import Operators.Negation

data 𝟘 {𝓤} : 𝓤 ̇ where

𝟘-induction : (A : 𝟘 {𝓤} → 𝓥 ̇ ) → (x : 𝟘) → A x
𝟘-induction A = λ ()

unique-from-𝟘 𝟘-elim : {A : 𝓥 ̇ } → 𝟘 {𝓤} → A
unique-from-𝟘 {𝓤} {𝓥} {A} = 𝟘-induction (λ _ → A)
𝟘-elim = unique-from-𝟘

-- 𝟘-is-prop : is-prop (𝟘 {𝓤})
-- 𝟘-is-prop {𝓤} x y = unique-from-𝟘 {𝓤} {𝓤} x

Not : 𝓤 ̇ → 𝓤 ̇
Not Y = Y → 𝟘 {𝓤₀}

open Op-Negation {{...}} public

instance
 Notⅈ : Op-Negation (𝓤 ̇)
 Notⅈ = record { ¬_ = Not }

{-# DISPLAY Not X = ¬ X #-}

¬¬_ ¬¬¬_ : 𝓤 ̇ → 𝓤 ̇
¬¬  A = ¬ (Not A)
¬¬¬ A = ¬(¬¬ A)

Neq : {X : 𝓤 ̇} → X → X → 𝓤 ̇
Neq x y = ¬ (Id _ x y)

_≠_ :  {X : 𝓤 ̇} → X → X → 𝓤 ̇
_≠_ = Neq

-- ×-𝟘-is-prop : {X : 𝓤 ̇ } → is-prop (X × 𝟘 {𝓥})
-- ×-𝟘-is-prop (x , z) _ = 𝟘-elim z

-- 𝟘-×-is-prop : {X : 𝓤 ̇ } → is-prop (𝟘 {𝓥} × X)
-- 𝟘-×-is-prop (z , x) _ = 𝟘-elim z

\end{code}
