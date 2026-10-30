module

public import Mathlib

public section

/-!
# The pairing of the twists in Conjecture 1.2 of David, Dunn, Hamieh and Lin: statements

This file is the statement surface for the Palomar registry. It restates, with their exact
library definitions, the objects the results are about, and states each result with `sorry`.
`Solution.lean` proves every statement below with the same name and type, using the development
in `QuarticPairing/`.

The normalized quartic Gauss sum `g̃` and the von Mangoldt function `Λ` of `ℤ[i]` are arbitrary
functions `g : GaussianInt → ℂ` and `Λ : GaussianInt → ℝ`. The hypothesis of every result is the
identity `g̃(c)² = -κ c/|c|` of David, Dunn, Hamieh and Lin (1.2), with `κ` a fixed unit, on the
support of `Λ` or off an exceptional set of small weight. That the actual quartic Gauss sum
satisfies it is the theorem (1.2) of their paper and is not formalized.

* `pointwise_pairing`, `pairing_of_twists`, `pairing_of_twists_defect`: the twist by `c̄/|c|`
  is conjugation, so `S_β(X; 1) = -κ conj S_β(X; 0)`.
* `pairing_identities`: `A(ν³, -m) = -κ conj A(ν, m)` for the twisted moments.
* `why_quartic`: if `|g| = 1` and `g^k = ξ`, then `ḡ = g^{k-1} ξ̄`.
* `conjecture12_inconsistent`, `conjecture12_inconsistent_of_defect`: Conjecture 1.2 fails.
-/

open Complex Finset Asymptotics

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


/-- **The pointwise pairing.** If `g̃(c) = 0` or `g̃(c)² = -κ c/|c|` with `|κ| = 1`, then
`g̃(c) (c̄/|c|) = -κ conj g̃(c)`. -/
theorem pointwise_pairing {g κ : ℂ} (hκ : ‖κ‖ = 1) {c : GaussianInt}
    (h : g = 0 ∨ g ^ 2 = -κ * unitDir c) :
    g * starRingEnd ℂ (unitDir c) = -κ * starRingEnd ℂ g := by
  sorry

/-- **The pairing of the twists.** If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support of `Λ`,
with `κ` a fixed unit, then `S_β(X; 1) = -κ conj S_β(X; 0)` for every `X`. -/
theorem pairing_of_twists (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    twistedSum g Λ β X 1 = -κ * starRingEnd ℂ (twistedSum g Λ β X 0) := by
  sorry

/-- **The pairing with an exceptional set.** If the identity holds off a set `E`, then
`|S_β(X; 1) + κ conj S_β(X; 0)|` is at most twice the weight of `E`. -/
theorem pairing_of_twists_defect (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    ‖twistedSum g Λ β X 1 + κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖ ≤
      2 * defectSum g Λ β E X := by
  sorry

/-- **The pairing identities.** For `k ∈ ℤ` (`m = 2k + 1`), if on the support of `w`
`g(c)² = -κ c/|c|` and `conj χ₃(c) = χ(c)` (as for `χ = (ν/c)₄`, `χ₃ = (ν³/c)₄`), then
`A(ν³, -m) = -κ conj A(ν, m)`. -/
theorem pairing_identities (χ χ₃ g : GaussianInt → ℂ) (w : GaussianInt → ℝ)
    (s : Finset GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (hχ : ∀ c ∈ s, w c ≠ 0 → starRingEnd ℂ (χ₃ c) = χ c)
    (h12 : ∀ c ∈ s, w c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (k : ℤ) :
    twistedAvg χ₃ g w s (-k - 1) = -κ * starRingEnd ℂ (twistedAvg χ g w s k) := by
  sorry

/-- **Why quartic.** If `|g| = 1` and `g^k = ξ` with `k ≥ 1`, then `ḡ = g^{k-1} ξ̄`. -/
theorem why_quartic {g ξ : ℂ} {k : ℕ} (hk : 1 ≤ k) (hg : ‖g‖ = 1) (h : g ^ k = ξ) :
    starRingEnd ℂ g = g ^ (k - 1) * starRingEnd ℂ ξ := by
  sorry

/-- **Conjecture 1.2 of David, Dunn, Hamieh and Lin is inconsistent with their identity (1.2).**
If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support of `Λ`, for a fixed unit `κ`, the conjecture
fails for the class `β`. -/
theorem conjecture12_inconsistent (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) :
    ¬ Conjecture12 g Λ β := by
  sorry

/-- **The same with an exceptional set** of weight `O(X^{1/2+ε})` for every `ε > 0`. -/
theorem conjecture12_inconsistent_of_defect (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ)
    (β : GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c)
    (hE : ∀ ε : ℝ, 0 < ε →
      (fun X : ℕ => defectSum g Λ β E X) =O[Filter.atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    ¬ Conjecture12 g Λ β := by
  sorry

end QuarticPairing
