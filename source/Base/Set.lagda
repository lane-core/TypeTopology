cites UF.Subsingletons

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Set where

open import Base.Type

𝟙-is-set : {!!}
𝟙-is-set = {!!}



\end{code}

A type is a set if all its identity types are subsingletons. In other
words, sets are types for which equality is a proposition (rather than
data or structure).

\begin{code}

is-h-isolated : {X : 𝓤 ̇ } → X → 𝓤 ̇
is-h-isolated x = ∀ {y} → is-prop (x ＝ y)

h-isolatedness-criterion : {X : 𝓤 ̇ } {x : X}
                         → is-prop (x ＝ x)
                         → is-h-isolated x
h-isolatedness-criterion {𝓤} {X} {x} i {y} = γ
 where
  γ : is-prop (x ＝ y)
  γ refl = i refl

is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = {x : X} → is-h-isolated x

-- hSet : (𝓤 : Universe) → 𝓤 ⁺ ̇
-- hSet 𝓤 = Σ A ꞉ 𝓤 ̇ , is-set A

-- underlying-set : hSet 𝓤 → 𝓤 ̇
-- underlying-set = pr₁

-- underlying-set-is-set : (ambient : hSet 𝓤) → is-set (underlying-set ambient)
-- underlying-set-is-set = pr₂

-- 𝟘-is-set : is-set (𝟘 {𝓤})
-- 𝟘-is-set {𝓤} {x} = 𝟘-elim x

-- refl-is-set : (X : 𝓤 ̇ )
--             → ((x : X) (p : x ＝ x) → p ＝ refl)
--             → is-set X
-- refl-is-set X r {x} p refl = r x p
