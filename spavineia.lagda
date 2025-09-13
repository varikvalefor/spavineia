\begin{code}
open import Level
  using (
    Level;
    _⊔_
  )
open import Data.Fin
  using (
    Fin
  )
open import Data.Nat
  using (
    ℕ
  )
open import Data.Maybe
  using (
    nothing;
    Maybe;
    maybe;
    just
  )

record PKED {lTg} {lTs} {j} : Set (Level.suc (lTg ⊔ lTs ⊔ j))
  where
  field
    Tg : Set lTg
    Ts : Set lTs
    J : Set j
    traji₁ : Maybe ℕ

  ES₁ : Set
  ES₁ = maybe Fin ℕ traji₁

  ES₂ : Set
  ES₂ = {!!}

  field
    enc : Tg → J → ES₁ → ES₂

O< : ∀ {lTg lTs j}
   → (p : PKED {lTg} {lTs} {j})
   → PKED.Tg p
   → PKED.J p
   → PKED.ES₁ p
   → PKED.ES₂ p
O< = λ p t j es → PKED.enc p t j es

<O : ∀ {lTg lTs j}
   → (p : PKED {lTg} {lTs} {j})
   → PKED.Ts p
   → PKED.J p
   → PKED.ES₁ p
   → Maybe (PKED.ES₂ p)
<O = {!!}

record PKSig : Set {!!}
  where

Cryptosystem : Set
Cryptosystem = {!!}
\end{code}
