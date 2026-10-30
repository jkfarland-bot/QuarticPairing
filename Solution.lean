module

public import QuarticPairing

public section

/-!
# Proved solution

Each declaration below has exactly the statement of its counterpart in `Challenge.lean` and is
proved from the development in `QuarticPairing/`. The definitions used in the statements come from
`QuarticPairing/Defs.lean` and are compared with the copies in `Challenge.lean`.
-/

open Complex Finset Asymptotics

noncomputable section

namespace QuarticPairing

/-- **The pointwise pairing.** If `g̃(c) = 0` or `g̃(c)² = -κ c/|c|` with `|κ| = 1`, then
`g̃(c) (c̄/|c|) = -κ conj g̃(c)`. -/
theorem pointwise_pairing {g κ : ℂ} (hκ : ‖κ‖ = 1) {c : GaussianInt}
    (h : g = 0 ∨ g ^ 2 = -κ * unitDir c) :
    g * starRingEnd ℂ (unitDir c) = -κ * starRingEnd ℂ g :=
  term_pairing hκ h

/-- **The pairing of the twists.** If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support of `Λ`,
with `κ` a fixed unit, then `S_β(X; 1) = -κ conj S_β(X; 0)` for every `X`. -/
theorem pairing_of_twists (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    twistedSum g Λ β X 1 = -κ * starRingEnd ℂ (twistedSum g Λ β X 0) :=
  twistedSum_one g Λ β hκ h12 X

/-- **The pairing with an exceptional set.** If the identity holds off a set `E`, then
`|S_β(X; 1) + κ conj S_β(X; 0)|` is at most twice the weight of `E`. -/
theorem pairing_of_twists_defect (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    ‖twistedSum g Λ β X 1 + κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖ ≤
      2 * defectSum g Λ β E X :=
  twistedSum_one_sub g Λ β hκ E h12 X

/-- **The pairing identities.** For `k ∈ ℤ` (`m = 2k + 1`), if on the support of `w`
`g(c)² = -κ c/|c|` and `conj χ₃(c) = χ(c)` (as for `χ = (ν/c)₄`, `χ₃ = (ν³/c)₄`), then
`A(ν³, -m) = -κ conj A(ν, m)`. -/
theorem pairing_identities (χ χ₃ g : GaussianInt → ℂ) (w : GaussianInt → ℝ)
    (s : Finset GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (hχ : ∀ c ∈ s, w c ≠ 0 → starRingEnd ℂ (χ₃ c) = χ c)
    (h12 : ∀ c ∈ s, w c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (k : ℤ) :
    twistedAvg χ₃ g w s (-k - 1) = -κ * starRingEnd ℂ (twistedAvg χ g w s k) :=
  twistedAvg_pairing χ χ₃ g w s hκ hχ h12 k

/-- **Why quartic.** If `|g| = 1` and `g^k = ξ` with `k ≥ 1`, then `ḡ = g^{k-1} ξ̄`. -/
theorem why_quartic {g ξ : ℂ} {k : ℕ} (hk : 1 ≤ k) (hg : ‖g‖ = 1) (h : g ^ k = ξ) :
    starRingEnd ℂ g = g ^ (k - 1) * starRingEnd ℂ ξ :=
  conj_eq_pow_mul hk hg h

/-- **Conjecture 1.2 of David, Dunn, Hamieh and Lin is inconsistent with their identity (1.2).**
If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support of `Λ`, for a fixed unit `κ`, the conjecture
fails for the class `β`. -/
theorem conjecture12_inconsistent (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) :
    ¬ Conjecture12 g Λ β :=
  not_conjecture12 g Λ β hκ h12

/-- **The same with an exceptional set** of weight `O(X^{1/2+ε})` for every `ε > 0`. -/
theorem conjecture12_inconsistent_of_defect (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ)
    (β : GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c)
    (hE : ∀ ε : ℝ, 0 < ε →
      (fun X : ℕ => defectSum g Λ β E X) =O[Filter.atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    ¬ Conjecture12 g Λ β :=
  not_conjecture12_of_defect g Λ β hκ E h12 hE

end QuarticPairing
