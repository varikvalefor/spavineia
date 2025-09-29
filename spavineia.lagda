\begin{code}
open import Level
  using (
    Level;
    _⊔_
  )
open import Data.Fin
  using (
    toℕ;
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
open import Function
  using (
    _∘_;
    _$_
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
    _%_
  )
open import Relation.Nullary
  using (
    Dec
  )
open import Data.Nat.Primality
  using (
    Prime
  )
open import Data.Nat.Coprimality
  using (
    coprime?;
    Coprime
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
open import Relation.Nullary.Decidable
  as R₀D
    using (
    )
open import Relation.Binary.PropositionalEquality
  as _≡_
  using (
    _≡_
  )
open import Relation.Binary.HeterogeneousEquality
  as _≅_
  using (
    _≅_
  )
\end{code}

\begin{code}
coerce : ∀ {a} → {A B : Set a} → A ≡ B → A → B
coerce _≡_.refl x = x
\end{code}

\begin{code}
record PKED (lTg lTs j : _) : Set (Level.suc (lTg ⊔ lTs ⊔ j))
  where
  field
    cmene : String
    Tg : Set lTg
    Ts : Set lTs
    J : Set j
    traji₁ : Maybe (Tg ⊎ Ts → J → ℕ)

  ES₁ : Tg ⊎ Ts → J → Set
  ES₁ g j = maybe (λ f → Fin $ f g j) ℕ traji₁

  ES₂ : Set
  ES₂ = ℕ

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
\end{code}

\begin{code}
O< : ∀ {lTg lTs j}
   → (p : PKED lTg lTs j)
   → (g : PKED.Tg p)
   → (j : PKED.J p)
   → PKED.ES₁ p (_⊎_.inj₁ g) j
   → PKED.ES₂ p
O< = PKED.enc
\end{code}

\begin{code}
<O : ∀ {lTg lTs j}
   → (p : PKED lTg lTs j)
   → (s : PKED.Ts p)
   → (j : PKED.J p)
   → PKED.ES₂ p
   → Maybe $ PKED.ES₁ p (_⊎_.inj₂ s) j
<O = PKED.dec?
\end{code}

\begin{code}
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
\end{code}

\begin{code}
module RSA where
  module T where
    record G : Set
      where
      field
        n e : ℕ
        n≢0 : R₀D.False $ n ℕ.≟ 0

    record S : Set
      where
      field
        p q : ℕ
        e : ℕ
        d : ℕ
        pPrime : Prime p
        qPrime : Prime q
      n = p ℕ.* q
      n≢0 : R₀D.False $ n ℕ.≟ 0
      n≢0 = {!!}
      eulerTotient : ℕ → ℕ
      eulerTotient = λ n → Data.List.length $ Data.List.filter (coprime? n) $ Data.List.upTo n
      field
        1<e<λ : (1 ℕ.< e) Σ.× (e ℕ.< eulerTotient n)
        λ' : ℕ
        λ'≡ : ℕ.suc λ' ≡ eulerTotient n
        mmi : (_≡_
                1
                (_%_
                  (d ℕ.* e)
                  (ℕ.suc λ')))

    M : S → G → Set
    M = λ s g → (G.n g ≡ S.n s) Σ.× (G.e g ≡ S.e s)

  Se : T.G → Set
  Se g = Fin (T.G.n g)

  Sd : T.S → Set
  Sd s = Fin (T.S.n s)

  O<' : (g : T.G) → Se g → ℕ
  O<' g m = _%_ m^e (T.G.n g) {≢0 = T.G.n≢0 g}
    where
    m^e = toℕ m ℕ.^ T.G.e g

  <O' : (s : T.S) → ℕ → Sd s
  <O' s c = Data.Nat.DivMod._mod_ (c ℕ.^ T.S.d s) (T.S.n s) {≢0 = T.S.n≢0 s}

  <O'∘O<' : (g : T.G)
          → (s : T.S)
          → T.M s g
          → (m : Se g)
          → toℕ m ≡ toℕ (<O' s (O<' g m))
  <O'∘O<' g s M m = _≡_.sym $ begin
    toℕ (<O' s $ O<' g m) ≡⟨ _≡_.refl ⟩
    toℕ (<O' s $ m^e %ng) ≡⟨ _≡_.refl ⟩
    toℕ (((m^e %ng) ℕ.^ T.S.d s) %ns) ≡⟨ {!!} ⟩
    toℕ (((m^e %ng) ℕ.^ T.S.d s) %ng') ≡⟨ {!!} ⟩
    toℕ ((m^e ℕ.^ T.S.d s) %ng') ≡⟨ {!!} ⟩
    toℕ m ∎
    where
    m' = toℕ m
    e = T.G.e g
    d = T.S.d s
    n₂ = T.S.n s
    m^e = m' ℕ.^ T.G.e g
    _%ng = λ x → _%_ x (T.G.n g) {T.G.n≢0 g}
    _%ng' = λ x → Data.Nat.DivMod._mod_ x (T.G.n g) {T.G.n≢0 g}
    _%ns = λ x → Data.Nat.DivMod._mod_ x (T.S.n s) {T.S.n≢0 s}
    Mm : (x m n₁ n₂ : ℕ)
       → x % ℕ.suc n₁ ≡ m
       → x % ℕ.suc n₂ ≡ m
       → x % (ℕ.suc n₁ ℕ.* ℕ.suc n₂) ≡ m
    Mm = {!!}
    open _≡_.≡-Reasoning
\end{code}

\begin{code}
instance
  rsaN : (n : ℕ) → PKED _ _ _
  rsaN n = record {
    cmene = "RSA-" ++ show n;
    Ts = RSA.T.S;
    Tg = RSA.T.G;
    traji₁ = just traji₁;
    J = Fin 1;
    M = Function.flip RSA.T.M;
    enc = λ g _ → RSA.O<' g;
    dec? = λ s _ → just ∘ RSA.<O' s;
    dec∘enc = {!!};
    ESd = λ g s (ns Σ., _) _ → _≡_.cong Fin ns
    }
    where
    traji₁ : RSA.T.G ⊎ RSA.T.S → Fin 1 → ℕ
    traji₁ (_⊎_.inj₁ g) _ = RSA.T.G.n g
    traji₁ (_⊎_.inj₂ s) _ = RSA.T.S.n s
\end{code}

\begin{code}
record ArkasaF (M₁l M₂l : _) : Set (Level.suc $ M₁l ⊔ M₂l)
  where
  field
    cmene : String
    M₁ : ℕ → Set M₁l
    M₂ : ℕ → Set M₂l
  ES₁ = Σ ℕ M₁
  ES₂ = Σ ℕ M₂
  field
    arkasa : ES₁ → ES₂
\end{code}

\begin{code}
record PKSig (lTg lTs j M₁l M₂l : _) : Set (Level.suc $ lTg ⊔ lTs ⊔ j ⊔ M₁l ⊔ M₂l)
  where
  field
    pked : PKED lTg lTs j
    arkasaf : ArkasaF M₁l M₂l
\end{code}

\begin{code}
sha256 : ArkasaF _ _
sha256 = record {
  cmene = "SHA-256";
  M₁ = λ x → ℕ;
  M₂ = ℕ._< (2 ℕ.^ 256);
  arkasa = {!!}
  }
\end{code}

\begin{code}
record Av (lTg lTs j : _) : Set (Level.suc (lTg ⊔ lTs ⊔ j))
  where
  field
    pked : List $ PKED lTg lTs j
\end{code}
\end{code}
