Pi type

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Pi where

open import Base.Type

Π : {X : 𝓤 ̇} (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} Y = (x : X) → Y x

-- We often write Π x ꞉ X , A x for Π A to make X explicit.
Pi : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Pi X Y = Π Y

syntax Pi A (λ x → b) = Π x ꞉ A , b

comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → ((y : Y) → Z y)
    → (f : X → Y) (x : X) → Z (f x)
comp g f = x ↦ g (f x)
--_∘_ = comp

{-# INLINE comp #-}

\end{code}

\begin{code}

open import Base.Operators public

instance
 Fun-Comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
          → Compose ((y : Y) → Z y) (λ _ → X → Y) (λ g f → (x : X) → Z (f x))
 _∘_ {{Fun-Comp}} = comp

{-# DISPLAY comp g f = g ∘ f #-}

\end{code}


Fixities:

\begin{code}

infixr 5 comp
infixr -1 Pi
infixr 5 _∘_
\end{code}
