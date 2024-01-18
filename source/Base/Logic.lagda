Logical connectives

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Base.Logic where

open import Base.Type
open import Base.Sigma
open import Base.Pi
open import Base.Id
open import Base.Empty

_↔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
A ↔ B = (A → B) × (B → A)

lr-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ↔ Y) → (X → Y)
lr-implication = pr₁

rl-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ↔ Y) → (Y → X)
rl-implication = pr₂

↔-sym : {X : 𝓤' ̇ } {Y : 𝓥' ̇ } → X ↔ Y → Y ↔ X
↔-sym (f , g) = (g , f)

↔-trans : {X : 𝓤' ̇ } {Y : 𝓥' ̇ } {Z : 𝓦' ̇ }
        → X ↔ Y → Y ↔ Z → X ↔ Z
↔-trans (f , g) (h , k) = (h ∘ f , g ∘ k)

↔-refl : {X : 𝓤' ̇ } → X ↔ X
↔-refl = (id , id)

is-nonempty : 𝓤 ̇ → 𝓤 ̇
is-nonempty = ¬¬_

dual : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (R : 𝓦 ̇ ) → (X → Y) → (Y → R) → (X → R)
dual R f p = p ∘ f

contrapositive : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → ¬ B → ¬ A
contrapositive = dual _

double-contrapositive : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → ¬¬ A → ¬¬ B
double-contrapositive = comp contrapositive contrapositive

¬¬-functor : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor = double-contrapositive

¬¬-kleisli : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli f ϕ h = ϕ (λ a → f a h)

¬¬-intro : {A : 𝓤 ̇ } → A → ¬¬ A
¬¬-intro x u = u x

three-negations-imply-one : {A : 𝓤 ̇ } → ¬¬¬ A → ¬ A
three-negations-imply-one = contrapositive ¬¬-intro

dne' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (¬¬ B → B) → ¬¬ A → B
dne' f h ϕ = h (λ g → ϕ (λ a → g (f a)))

dne : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → ¬ B) → ¬¬ A → ¬ B
dne f ϕ b = ϕ (λ a → f a b)

double-negation-unshift : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ¬¬ ((x : X) → A x) → (x : X) → ¬¬ (A x)
double-negation-unshift f x g = f (λ h → g (h x))

dnu : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → ¬¬ (A × B) → ¬¬ A × ¬¬ B
dnu φ = (¬¬-functor pr₁ φ) , (¬¬-functor pr₂ φ)

und : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → ¬¬ A × ¬¬ B → ¬¬ (A × B)
und (φ , γ) w = γ (λ y → φ (λ x → w (x , y)))

¬¬-stable : 𝓤 ̇ → 𝓤 ̇
¬¬-stable A = ¬¬ A → A

¬-is-¬¬-stable : {A : 𝓤 ̇ } → ¬¬-stable (¬ A)
¬-is-¬¬-stable = three-negations-imply-one

Π-is-¬¬-stable : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ }
               → ((a : A) → ¬¬-stable (B a))
               → ¬¬-stable (Π B)
Π-is-¬¬-stable f ϕ a = f a (λ v → ϕ (λ g → v (g a)))

→-is-¬¬-stable : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
               → ¬¬-stable B
               → ¬¬-stable (A → B)
→-is-¬¬-stable f = Π-is-¬¬-stable (λ _ → f)

×-is-¬¬-stable : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
               → ¬¬-stable A
               → ¬¬-stable B
               → ¬¬-stable (A × B)
×-is-¬¬-stable f g ϕ = f (λ v → ϕ (λ (a , b) → v a)) ,
                       g (λ v → ϕ (λ (a , b) → v b))

negation-of-implication :  {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                        → ¬ (A → B)
                        → ¬¬ A × ¬ B
negation-of-implication u = (λ v → u (λ a → 𝟘-elim (v a))) ,
                            (λ b → u (λ a → b))

negation-of-implication-converse :  {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                                 → ¬¬ A × ¬ B
                                 → ¬ (A → B)
negation-of-implication-converse (u , v) f = u (λ a → v (f a))

Double-negation-of-implication← : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                                  {R : 𝓦 ̇ } {S : 𝓣 ̇ } {T : 𝓣' ̇ }
                                → (((A → B) → T) → S)
                                → (((A → S) → R) × (B → T)) → R
Double-negation-of-implication← f g = pr₁ g (λ a → f (λ h → pr₂ g (h a)))

Double-negation-of-implication→ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                                  (R : 𝓦 ̇ ) {S : 𝓣 ̇ } {T : 𝓣' ̇ } {U : 𝓣' ̇ }
                                → (S → B)
                                → ((((A → S) → T) × (B → T)) → U)
                                → ((A → B) → T) → U
Double-negation-of-implication→ R k f g = f ((λ h → g (λ a → k (h a))) ,
                                             (λ b → g (λ a → b)))

double-negation-of-implication← : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → ¬¬ (A → B) → ¬ (¬¬ A × ¬ B)
double-negation-of-implication← = Double-negation-of-implication←

double-negation-of-implication→ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → ¬ (¬¬ A × ¬ B) → ¬¬ (A → B)
double-negation-of-implication→ f g = Double-negation-of-implication→ (𝟘 {𝓤₀}) 𝟘-elim f g

not-equivalent-to-own-negation' : {A : 𝓤 ̇ } {R : 𝓥 ̇ } → (A ↔ (A → R)) → R
not-equivalent-to-own-negation' (f , g) = f (g (λ a → f a a)) (g (λ a → f a a))

not-equivalent-to-own-negation : {A : 𝓤 ̇ } → ¬ (A ↔ ¬ A)
not-equivalent-to-own-negation = not-equivalent-to-own-negation'

not-Σ-implies-Π-not : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                    → ¬ (Σ x ꞉ X , A x)
                    → (x : X) → ¬ (A x)
not-Σ-implies-Π-not = curry

Π-not-implies-not-Σ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                    → ((x : X) → ¬ (A x))
                    → ¬ (Σ x ꞉ X , A x)
Π-not-implies-not-Σ = uncurry

Π-implies-not-Σ-not : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                    → ((x : X) → A x)
                    → ¬ (Σ x ꞉ X , ¬ (A x))
Π-implies-not-Σ-not f (x , ν) = ν (f x)

not-Π-not-not-implies-not-not-Σ-not : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                                    → ¬ ((x : X) → ¬¬ (A x))
                                    → ¬¬ (Σ x ꞉ X , ¬ (A x))
not-Π-not-not-implies-not-not-Σ-not = contrapositive not-Σ-implies-Π-not

not-Π-implies-not-not-Σ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                        → ((x : X) → ¬¬-stable (A x))
                        → ¬ ((x : X) → A x)
                        → ¬¬ (Σ x ꞉ X , ¬ (A x))
not-Π-implies-not-not-Σ f g h = g (λ x → f x (λ u → h (x , u)))

\end{code}

Notation to try to make proofs readable:

\begin{code}

contradiction : 𝓤₀ ̇
contradiction = 𝟘

have_which-is-impossible-by_ : {A : 𝓤 ̇ } {B : 𝓦 ̇ }
                             → A → (A → 𝟘 {𝓤₀}) → B
have a which-is-impossible-by ν = 𝟘-elim (ν a)


have_which-contradicts_ : {A : 𝓤 ̇ } {B : 𝓦 ̇ }
                        → (A → 𝟘 {𝓤₀}) → A → B
have ν which-contradicts a = 𝟘-elim (ν a)

\end{code}

We use the following to indicate the type of a subterm (where "∶"
(typed "\:" in emacs) is not the same as ":"):

\begin{code}

-id : (X : 𝓤 ̇ ) → X → X
-id X x = x

syntax -id X x = x ∶ X

\end{code}

This is used for efficiency as a substitute for lazy "let" (or "where"):

\begin{code}

case_of_ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → (a : A) → ((a : A) → B a) → B a
case x of f = f x

Case_of_ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → (a : A) → ((x : A) → a ＝ x → B a) → B a
Case x of f = f x refl

{-# NOINLINE case_of_ #-}

\end{code}

Notation to try to make proofs readable:

\begin{code}

need_which-is-given-by_ : (A : 𝓤 ̇ ) → A → A
need A which-is-given-by a = a

have_by_ : (A : 𝓤 ̇ ) → A → A
have A by a = a

have_so_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A → B → B
have a so b = b

have_so-use_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A → B → B
have a so-use b = b

have_and_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A → B → B
have a and b = b

apply_to_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → A → B
apply f to a = f a

have_so-apply_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A → (A → B) → B
have a so-apply f = f a

assume-then : (A : 𝓤 ̇ ) {B : A → 𝓥 ̇ } → ((a : A) → B a) → (a : A) → B a
assume-then A f x = f x

syntax assume-then A (λ x → b) = assume x ∶ A then b

assume-and : (A : 𝓤 ̇ ) {B : A → 𝓥 ̇ } → ((a : A) → B a) → (a : A) → B a
assume-and A f x = f x

syntax assume-and A (λ x → b) = assume x ∶ A and b

mapsto : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → ((a : A) → B a) → (a : A) → B a
mapsto f = f

syntax mapsto (λ x → b) = x ↦ b

infixr 10 mapsto

Mapsto : (A : 𝓤 ̇ ) {B : A → 𝓥 ̇ } → ((a : A) → B a) → (a : A) → B a
Mapsto A f = f

syntax Mapsto A (λ x → b) = x ꞉ A ↦ b

infixr 10 Mapsto

\end{code}

Fixities:

\begin{code}

infix -1 _↔_

\end{code}
