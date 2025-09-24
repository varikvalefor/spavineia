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
  as ℕ
  using (
    ℕ
  )
open import Data.Sum
  as _⊎_
  using (
    _⊎_
  )
open import Data.List
  using (
    List
  )
open import Data.Maybe
  using (
    nothing;
    Maybe;
    maybe;
    just
  )
open import Data.String
  using (
    String
  )
open import Data.Product
  as Σ
  using (
    Σ
  )
open import Data.Nat.DivMod
  using (
  )
open import Relation.Nullary
  using (
    Dec
  )
open import Truthbrary.Record.SR
  using (
    show;
    showNat
  )
open import Truthbrary.Record.LLC
  using (
    _++_;
    liliString
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
  )

coerce : ∀ {a} → {A B : Set a} → A ≡ B → A → B
coerce _≡_.refl x = x

record PKED (lTg lTs j : _) : Set (Level.suc (lTg ⊔ lTs ⊔ j))
  where
  field
    cmene : String
    Tg : Set lTg
    Ts : Set lTs
    J : Set j
    traji₁ : Maybe (Tg ⊎ Ts → J → ℕ)
    traji₂ : Maybe ℕ

  ES₁ : Tg ⊎ Ts → J → Set
  ES₁ g j = maybe Fin ℕ (Data.Maybe.map (λ f → f g j) traji₁)

  ES₂ : Set
  ES₂ = maybe Fin ℕ traji₂

  field
    M : Tg → Ts → Set
    ESd : (g : Tg)
        → (s : Ts)
        → M g s
        → (j : J)
        → ES₁ (_⊎_.inj₁ g) j ≡ ES₁ (_⊎_.inj₂ s) j
    enc : (g : Tg) → (j : J) → ES₁ (_⊎_.inj₁ g) j → ES₂
    dec? : (s : Ts) → (j : J) → ES₂ → Maybe (ES₁ (_⊎_.inj₂ s) j)

  field
    dec∘enc : (tg : Tg)
            → (ts : Ts)
            → (j : J)
            → (es : ES₁ (_⊎_.inj₁ tg) j)
            → (m : M tg ts)
            → let es' = coerce (ESd tg ts m j) es in
              just es' ≡ dec? ts j (enc tg j es)

O< : ∀ {lTg lTs j}
   → (p : PKED lTg lTs j)
   → (g : PKED.Tg p)
   → (j : PKED.J p)
   → PKED.ES₁ p (_⊎_.inj₁ g) j
   → PKED.ES₂ p
O< = PKED.enc

<O : ∀ {lTg lTs j}
   → (p : PKED lTg lTs j)
   → (s : PKED.Ts p)
   → (j : PKED.J p)
   → PKED.ES₂ p
   → Maybe (PKED.ES₁ p (_⊎_.inj₂ s) j)
<O = PKED.dec?

<O∘O< : ∀ {lTg lTs j}
      → (p : PKED lTg lTs j)
      → (tg : PKED.Tg p)
      → (ts : PKED.Ts p)
      → (j : PKED.J p)
      → (es₁ : PKED.ES₁ p (_⊎_.inj₁ tg) j)
      → (m : PKED.M p tg ts)
      → let es₁' = coerce (PKED.ESd p tg ts m j) es₁ in
        just es₁' ≡ <O p ts j (O< p tg j es₁)
<O∘O< = PKED.dec∘enc

module RSA where
  module T where
    record G : Set
      where
      field
        n e : ℕ

    record S : Set
      where
      field
        p q : ℕ
        e : ℕ
        d : ℕ
      n = p ℕ.* q
      eulerTotient : ℕ → ℕ
      eulerTotient = {!!}
      field
        1<e<λ : (1 ℕ.< e) Σ.× (e ℕ.< eulerTotient n)
        ≢0 : _
        mmi : (_≡_
                1
                (Data.Nat.DivMod._%_
                  (d ℕ.* e)
                  (eulerTotient n)
                  {≢0 = ≢0}))

    M : S → G → Set
    M = λ s g → (G.n g ≡ S.n s) Σ.× (G.e g ≡ S.e s)

instance
  rsaN : (n : ℕ) → PKED _ _ _
  rsaN n = record {
    cmene = "RSA-" ++ show n;
    Ts = RSA.T.S;
    Tg = RSA.T.G;
    traji₁ = just traji₁;
    traji₂ = just {!!};
    J = Fin 1;
    M = λ x z → RSA.T.M z x;
    enc = {!!};
    dec? = {!!};
    dec∘enc = {!!};
    ESd = {!!}
    }
    where
    traji₁ : RSA.T.G ⊎ RSA.T.S → Fin 1 → ℕ
    traji₁ (_⊎_.inj₁ g) _ = RSA.T.G.n g
    traji₁ (_⊎_.inj₂ s) _ = RSA.T.S.n s

record ArkasaF (M₁l M₂l : _) : Set (Level.suc (M₁l ⊔ M₂l))
  where
  field
    cmene : String
    M₁ : ℕ → Set M₁l
    M₂ : ℕ → Set M₂l
  ES₁ = Σ ℕ M₁
  ES₂ = Σ ℕ M₂
  field
    arkasa : ES₁ → ES₂

record PKSig (lTg lTs j M₁l M₂l : _) : Set (Level.suc (lTg ⊔ lTs ⊔ j ⊔ M₁l ⊔ M₂l))
  where
  field
    pked : PKED lTg lTs j
    arkasaf : ArkasaF M₁l M₂l

sha256 : ArkasaF _ _
sha256 = record {
  cmene = "SHA-256";
  M₁ = λ x → ℕ;
  M₂ = ℕ._< (2 ℕ.^ 256);
  arkasa = {!!}
  }

record Av (lTg lTs j : _) : Set (Level.suc (lTg ⊔ lTs ⊔ j))
  where
  field
    pked : List (PKED lTg lTs j)
\end{code}
