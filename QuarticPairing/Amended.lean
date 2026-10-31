module

public import QuarticPairing.Inconsistency

@[expose] public section

/-!
# The amended conjecture

In the amended conjecture the twist `ℓ = 1` carries the main term `-κ conj(b) X^{3/4}`.

* `amendedMain_reflect`: the main terms satisfy `M(1 - ℓ) = -κ conj M(ℓ)`, as the sums do;
* `conjecture12Amended_iff`: under the identity `g̃(c)² = -κ c/|c|`, the amended conjecture is
  equivalent to its cases `ℓ ≤ 0`, so the identity imposes nothing on it beyond them;
* `main_term_forced_of_pairing`: under the identity, main terms `b X^{3/4}` at `ℓ = 0` and `b' X^{3/4}`
  at `ℓ = 1`, with errors `O(X^{1/2+ε})`, force `b' = -κ conj b`. So the amendment is the only
  form of the main term at `ℓ = 1` compatible with the case `ℓ = 0`.
-/

open Complex Filter Asymptotics Finset

noncomputable section

namespace QuarticPairing

lemma isBigO_neg_mul_conj {κ : ℂ} (hκ : ‖κ‖ = 1) {f : ℕ → ℂ} {u : ℕ → ℝ}
    (h : f =O[atTop] u) : (fun X => -κ * starRingEnd ℂ (f X)) =O[atTop] u := by
  refine IsBigO.of_norm_left ?_
  have : (fun X => ‖-κ * starRingEnd ℂ (f X)‖) = fun X => ‖f X‖ :=
    funext fun X => by rw [norm_mul, norm_neg, hκ, one_mul, Complex.norm_conj]
  rw [this]; exact h.norm_left

/-- The main terms of the amended conjecture satisfy `M(1 - ℓ) = -κ conj M(ℓ)`. -/
lemma amendedMain_reflect {κ : ℂ} (hκ : ‖κ‖ = 1) (b : ℂ) (X : ℕ) (ℓ : ℤ) :
    amendedMain κ b X (1 - ℓ) = -κ * starRingEnd ℂ (amendedMain κ b X ℓ) := by
  have hκκ := mul_conj_self_eq_one hκ
  unfold amendedMain
  by_cases h0 : ℓ = 0
  · subst h0
    simp [Complex.conj_ofReal]
    ring
  by_cases h1 : ℓ = 1
  · subst h1
    simp only [sub_self, ite_true, one_ne_zero, ite_false, map_mul, map_neg, Complex.conj_conj,
      Complex.conj_ofReal]
    linear_combination (-(b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ))) * hκκ
  · have h2 : (1 - ℓ) ≠ 0 := by omega
    have h3 : (1 - ℓ) ≠ 1 := by omega
    simp [h0, h1, h2, h3]

/-- Under the identity, the error of the amended conjecture at `1 - ℓ` is `-κ` times the conjugate
of the error at `ℓ`, so the two are `O` of the same function together. -/
lemma amended_reflect_iff (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (b : ℂ)
    (u : ℕ → ℝ) (ℓ : ℤ) :
    (fun X : ℕ => twistedSum g Λ β X (1 - ℓ) - amendedMain κ b X (1 - ℓ)) =O[atTop] u ↔
      (fun X : ℕ => twistedSum g Λ β X ℓ - amendedMain κ b X ℓ) =O[atTop] u := by
  have he : (fun X : ℕ => twistedSum g Λ β X (1 - ℓ) - amendedMain κ b X (1 - ℓ)) =
      fun X => -κ * starRingEnd ℂ (twistedSum g Λ β X ℓ - amendedMain κ b X ℓ) := by
    funext X
    rw [twistedSum_reflect g Λ β hκ h12 X ℓ, amendedMain_reflect hκ b X ℓ, map_sub]
    ring
  rw [he]
  constructor
  · intro h
    have := isBigO_neg_mul_conj hκ h
    refine this.congr_left fun X => ?_
    have hκκ := mul_conj_self_eq_one hκ
    simp only [map_mul, map_neg, Complex.conj_conj]
    linear_combination (twistedSum g Λ β X ℓ - amendedMain κ b X ℓ) * hκκ
  · exact isBigO_neg_mul_conj hκ

/-- **The amended conjecture is consistent with the identity.** If `g̃(c)² = -κ c/|c|` (or
`g̃(c) = 0`) on the support of `Λ`, the amended conjecture is equivalent to its cases `ℓ ≤ 0`: the
cases `ℓ ≥ 1` follow from them. -/
theorem conjecture12Amended_iff (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) :
    Conjecture12Amended g Λ β κ ↔
      ∃ b : ℂ, b ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∀ ℓ : ℤ, ℓ ≤ 0 →
        (fun X : ℕ => twistedSum g Λ β X ℓ - amendedMain κ b X ℓ)
          =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε)) := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, fun ε hε ℓ _ => h ε hε ℓ⟩
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, fun ε hε ℓ => ?_⟩
    by_cases hℓ : ℓ ≤ 0
    · exact h ε hε ℓ hℓ
    · have := (amended_reflect_iff g Λ β hκ h12 b _ (1 - ℓ)).2 (h ε hε (1 - ℓ) (by omega))
      rwa [sub_sub_cancel] at this

/-- **The main term at `ℓ = 1` is forced.** If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support
of `Λ`, and `S_β(X; 0) = b X^{3/4} + O(X^{1/2+ε})` and `S_β(X; 1) = b' X^{3/4} + O(X^{1/2+ε})`
for every `ε > 0`, then `b' = -κ conj b`. -/
theorem main_term_forced_of_pairing (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (b b' : ℂ)
    (h0 : ∀ ε : ℝ, 0 < ε → (fun X : ℕ => twistedSum g Λ β X 0 -
      b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε)))
    (h1 : ∀ ε : ℝ, 0 < ε → (fun X : ℕ => twistedSum g Λ β X 1 -
      b' * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    b' = -κ * starRingEnd ℂ b := by
  have he : (1 : ℝ) / 2 + 1 / 8 = 5 / 8 := by norm_num
  have a0 := h0 (1 / 8) (by norm_num)
  have a1 := h1 (1 / 8) (by norm_num)
  rw [he] at a0 a1
  have hs := (a1.neg_left.add (isBigO_neg_mul_conj hκ a0))
  have hz : b' + κ * starRingEnd ℂ b = 0 := by
    refine eq_zero_of_isBigO (hs.congr_left fun X => ?_)
    rw [twistedSum_one g Λ β hκ h12 X, map_sub, map_mul, Complex.conj_ofReal]
    ring
  linear_combination hz
