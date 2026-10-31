module

public import Mathlib

@[expose] public section

/-!
# Definitions

The objects of Conjecture 1.2 of David, Dunn, Hamieh and Lin (*Quartic Gauss sums over primes and
metaplectic theta functions*, arXiv:2306.11875). The normalized quartic Gauss sum `g̃` and the von
Mangoldt function `Λ` of `ℤ[i]` enter only as functions `g : GaussianInt → ℂ` and
`Λ : GaussianInt → ℝ`; the results assume of them only the identity `g̃(c)² = -κ c/|c|` of DDHL
(1.2), so no quartic residue symbol is defined here.

* `unitDir c = c/|c|`, viewed in `ℂ` (and `0` at `c = 0`).
* `normBall X` is the finite set of Gaussian integers of norm at most `X`.
* `twistedSum g Λ β X ℓ = ∑_{N(c) ≤ X, c ≡ β (mod 4)} g(c) (c̄/|c|)^ℓ Λ(c)`.
* `Conjecture12 g Λ β` is DDHL's Conjecture 1.2 for the class `β`, along integer `X`.
* `amendedMain κ b X ℓ` is the main term `b X^{3/4}` at `ℓ = 0`, `-κ conj(b) X^{3/4}` at `ℓ = 1`
  and `0` otherwise, and `Conjecture12Amended g Λ β κ` is the conjecture with these main terms.
* `defectSum g Λ β E X = ∑ |g(c)| |Λ(c)|` over the `c` of the class with `N(c) ≤ X` in an
  exceptional set `E`.
* `twistedAvg χ g w s k = ∑_{c ∈ s} conj(χ(c)) g(c) (c/|c|)^k w(c)`, the weighted moments of the
  pairing identities, with `χ(c)` standing for a residue symbol `(ν/c)₄`.
-/

open Complex Finset

noncomputable section

namespace QuarticPairing

/-- The direction `c/|c|` of a Gaussian integer, as a complex number (`0` at `c = 0`). -/
def unitDir (c : GaussianInt) : ℂ := GaussianInt.toComplex c / ‖GaussianInt.toComplex c‖

/-- The Gaussian integers of norm at most `X`. -/
def normBall (X : ℕ) : Finset GaussianInt :=
  ((Icc (-(X : ℤ)) X ×ˢ Icc (-(X : ℤ)) X).image fun ab => (⟨ab.1, ab.2⟩ : GaussianInt)).filter
    fun c => c.norm ≤ X

open Classical in
/-- `S_β(X; ℓ) = ∑_{N(c) ≤ X, c ≡ β (mod 4)} g(c) (c̄/|c|)^ℓ Λ(c)`. -/
def twistedSum (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) (X : ℕ) (ℓ : ℤ) :
    ℂ :=
  ∑ c ∈ (normBall X).filter (fun c => (4 : GaussianInt) ∣ c - β),
    g c * (starRingEnd ℂ (unitDir c)) ^ ℓ * (Λ c : ℂ)

/-- **Conjecture 1.2 of David, Dunn, Hamieh and Lin**, for the class `β` and along integer `X`:
there is `b ≠ 0` such that for every `ε > 0` and every `ℓ ∈ ℤ`,
`S_β(X; ℓ) = b X^{3/4} + O(X^{1/2+ε})` if `ℓ = 0` and `S_β(X; ℓ) = O(X^{1/2+ε})` otherwise. -/
def Conjecture12 (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) : Prop :=
  ∃ b : ℂ, b ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∀ ℓ : ℤ,
    (fun X : ℕ => twistedSum g Λ β X ℓ -
        (if ℓ = 0 then b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ) else 0))
      =O[Filter.atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))

/-- The main term of the amended conjecture: `b X^{3/4}` at `ℓ = 0`, `-κ conj(b) X^{3/4}` at
`ℓ = 1`, and `0` for the other `ℓ`. -/
def amendedMain (κ b : ℂ) (X : ℕ) (ℓ : ℤ) : ℂ :=
  if ℓ = 0 then b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)
  else if ℓ = 1 then -κ * starRingEnd ℂ b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ) else 0

/-- **The amended conjecture**, for the class `β` and along integer `X`: there is `b ≠ 0` such
that for every `ε > 0` and every `ℓ ∈ ℤ`, `S_β(X; ℓ) = b X^{3/4} + O(X^{1/2+ε})` if `ℓ = 0`,
`S_β(X; ℓ) = -κ conj(b) X^{3/4} + O(X^{1/2+ε})` if `ℓ = 1`, and `S_β(X; ℓ) = O(X^{1/2+ε})`
otherwise. For the quartic Gauss sum `κ = 1`. -/
def Conjecture12Amended (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) (κ : ℂ) :
    Prop :=
  ∃ b : ℂ, b ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∀ ℓ : ℤ,
    (fun X : ℕ => twistedSum g Λ β X ℓ - amendedMain κ b X ℓ)
      =O[Filter.atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))

open Classical in
/-- The weight `∑ |g(c)| |Λ(c)|` of the elements `c` of the class `β` with `N(c) ≤ X` that lie in
an exceptional set `E`. -/
def defectSum (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    (E : GaussianInt → Prop) (X : ℕ) : ℝ :=
  ∑ c ∈ ((normBall X).filter (fun c => (4 : GaussianInt) ∣ c - β)).filter E, ‖g c‖ * |Λ c|

/-- The weighted moment `∑_{c ∈ s} conj(χ(c)) g(c) (c/|c|)^k w(c)`. With `χ(c) = (ν/c)₄` and
`k = (m - 1)/2` this is the sum behind `A_β(ν, m)` in the manuscript. -/
def twistedAvg (χ g : GaussianInt → ℂ) (w : GaussianInt → ℝ) (s : Finset GaussianInt) (k : ℤ) :
    ℂ :=
  ∑ c ∈ s, starRingEnd ℂ (χ c) * g c * unitDir c ^ k * (w c : ℂ)

end QuarticPairing
