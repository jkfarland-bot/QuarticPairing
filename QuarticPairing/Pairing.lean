module

public import QuarticPairing.Defs

@[expose] public section

/-!
# The pairing of the twists

If `g² = -κθ` with `|θ| = |κ| = 1`, then `g θ̄ = -κ ḡ`. With `θ = c/|c|` and `g = g̃(c)` this turns
the twist by `c̄/|c|` into conjugation:

* `term_pairing`: `g̃(c) (c̄/|c|) = -κ conj g̃(c)`;
* `twistedSum_one`: `S_β(X; 1) = -κ conj S_β(X; 0)` when the identity holds on the support of `Λ`;
* `twistedSum_reflect`: more generally `S_β(X; 1 - ℓ) = -κ conj S_β(X; ℓ)` for every `ℓ`;
* `twistedSum_one_sub`: in general `S_β(X; 1) + κ conj S_β(X; 0)` is at most twice the weight of
  the exceptional set where the identity is not assumed;
* `twistedAvg_pairing`: the moments `A(ν, m)`, `m` odd, satisfy `A(ν³, -m) = -κ conj A(ν, m)`
  whenever `conj (ν³/c)₄ = (ν/c)₄`;
* `conj_eq_pow_mul`: if `|g| = 1` and `g^k = ξ`, then `ḡ = g^{k-1} ξ̄`, so conjugation returns
  to the first moment exactly when `k = 2`.
-/

open Complex Finset

noncomputable section

namespace QuarticPairing

lemma mul_conj_self_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z * starRingEnd ℂ z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp

/-- If `|θ| = |κ| = 1` and `g² = -κθ` (or `g = 0`), then `g θ̄ = -κ ḡ`. -/
lemma mul_conj_eq_neg_conj {g θ κ : ℂ} (hθ : ‖θ‖ = 1) (hκ : ‖κ‖ = 1)
    (h : g = 0 ∨ g ^ 2 = -κ * θ) : g * starRingEnd ℂ θ = -κ * starRingEnd ℂ g := by
  rcases h with h | h
  · simp [h]
  · have hκκ := mul_conj_self_eq_one hκ
    have hθ' : θ = -g ^ 2 * starRingEnd ℂ κ := by
      linear_combination (starRingEnd ℂ κ) * h - θ * hκκ
    have hn : ‖g‖ ^ 2 = 1 := by
      have := congrArg norm hθ'
      rw [hθ, norm_mul, norm_neg, norm_pow, Complex.norm_conj, hκ, mul_one] at this
      exact this.symm
    have hgg : g * starRingEnd ℂ g = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    rw [hθ', map_mul, map_neg, map_pow, Complex.conj_conj]
    linear_combination (-(κ * starRingEnd ℂ g)) * hgg

lemma toComplex_ne_zero {c : GaussianInt} (hc : c ≠ 0) : GaussianInt.toComplex c ≠ 0 := by
  rwa [Ne, map_eq_zero_iff _ GaussianInt.toComplex_injective]

lemma norm_unitDir {c : GaussianInt} (hc : c ≠ 0) : ‖unitDir c‖ = 1 := by
  rw [unitDir, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.2 (toComplex_ne_zero hc))]

lemma unitDir_zero : unitDir 0 = 0 := by simp [unitDir]

lemma norm_unitDir_le (c : GaussianInt) : ‖unitDir c‖ ≤ 1 := by
  by_cases hc : c = 0
  · subst hc; simp [unitDir_zero]
  · rw [norm_unitDir hc]

/-- **The pointwise pairing.** If `g̃(c) = 0` or `g̃(c)² = -κ c/|c|` with `|κ| = 1`, then
`g̃(c) (c̄/|c|) = -κ conj g̃(c)`. -/
theorem term_pairing {g κ : ℂ} (hκ : ‖κ‖ = 1) {c : GaussianInt}
    (h : g = 0 ∨ g ^ 2 = -κ * unitDir c) :
    g * starRingEnd ℂ (unitDir c) = -κ * starRingEnd ℂ g := by
  by_cases hc : c = 0
  · subst hc
    rw [unitDir_zero] at h ⊢
    rcases h with h | h
    · simp [h]
    · have : g = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by simpa using h)
      simp [this]
  · exact mul_conj_eq_neg_conj (norm_unitDir hc) hκ h

/-- The summand identity behind `twistedSum_one`. -/
lemma term_one_add (g κ : ℂ) (hκ : ‖κ‖ = 1) (c : GaussianInt) (Λ : ℝ)
    (h : Λ ≠ 0 → g = 0 ∨ g ^ 2 = -κ * unitDir c) :
    g * starRingEnd ℂ (unitDir c) ^ (1 : ℤ) * (Λ : ℂ) +
      κ * starRingEnd ℂ (g * starRingEnd ℂ (unitDir c) ^ (0 : ℤ) * (Λ : ℂ)) = 0 := by
  by_cases hΛ : Λ = 0
  · simp [hΛ]
  · rw [zpow_one, zpow_zero, mul_one, term_pairing hκ (h hΛ), map_mul, Complex.conj_ofReal]
    ring

open Classical in
/-- **The pairing of the twists.** If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support of `Λ`,
with `κ` a fixed unit, then `S_β(X; 1) = -κ conj S_β(X; 0)` for every `X`. -/
theorem twistedSum_one (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    twistedSum g Λ β X 1 = -κ * starRingEnd ℂ (twistedSum g Λ β X 0) := by
  rw [← sub_eq_zero, show ∀ a b : ℂ, a - -κ * b = a + κ * b from fun a b => by ring]
  unfold twistedSum
  rw [map_sum, mul_sum, ← sum_add_distrib]
  exact sum_eq_zero fun c _ => term_one_add (g c) κ hκ c (Λ c) (h12 c)

open Classical in
/-- **The pairing with an exceptional set.** If the identity holds off a set `E`, then
`|S_β(X; 1) + κ conj S_β(X; 0)|` is at most twice the weight of `E`. -/
theorem twistedSum_one_sub (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) :
    ‖twistedSum g Λ β X 1 + κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖ ≤
      2 * defectSum g Λ β E X := by
  unfold twistedSum defectSum
  set s := (normBall X).filter (fun c => (4 : GaussianInt) ∣ c - β)
  rw [map_sum, mul_sum, ← sum_add_distrib, ← sum_filter_add_sum_filter_not s E]
  rw [sum_eq_zero (s := s.filter fun c => ¬ E c) (fun c hc =>
    term_one_add (g c) κ hκ c (Λ c) (h12 c (mem_filter.1 hc).2)), add_zero, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_conj, zpow_one, zpow_zero, mul_one,
    Complex.norm_real, Real.norm_eq_abs, hκ, one_mul]
  have h1 := norm_unitDir_le c
  have h2 : 0 ≤ ‖g c‖ := norm_nonneg _
  have h3 : 0 ≤ |Λ c| := abs_nonneg _
  nlinarith [mul_nonneg h2 h3, mul_le_mul_of_nonneg_left h1 h2]

lemma unitDir_ne_zero_of {g κ : ℂ} {c : GaussianInt} (hg : g ≠ 0) (h : g ^ 2 = -κ * unitDir c) :
    unitDir c ≠ 0 := by
  intro h0; simp [h0] at h; exact hg h

/-- The summand identity behind `twistedSum_reflect`. -/
lemma term_reflect (g κ : ℂ) (hκ : ‖κ‖ = 1) (c : GaussianInt) (Λ : ℝ)
    (h : Λ ≠ 0 → g = 0 ∨ g ^ 2 = -κ * unitDir c) (ℓ : ℤ) :
    g * starRingEnd ℂ (unitDir c) ^ (1 - ℓ) * (Λ : ℂ) =
      -κ * starRingEnd ℂ (g * starRingEnd ℂ (unitDir c) ^ ℓ * (Λ : ℂ)) := by
  by_cases hΛ : Λ = 0
  · simp [hΛ]
  rcases h hΛ with hg | hg
  · simp [hg]
  by_cases hg0 : g = 0
  · simp [hg0]
  have hθ0 := unitDir_ne_zero_of hg0 hg
  have hc0 : c ≠ 0 := by rintro rfl; exact hθ0 unitDir_zero
  have hθ := norm_unitDir hc0
  have hpair := mul_conj_eq_neg_conj hθ hκ (Or.inr hg)
  have hκκ := mul_conj_self_eq_one hκ
  have hθθ := mul_conj_self_eq_one hθ
  have hφ0 : starRingEnd ℂ (unitDir c) ≠ 0 := (map_ne_zero _).2 hθ0
  have hθinv : unitDir c = (starRingEnd ℂ (unitDir c))⁻¹ := eq_inv_of_mul_eq_one_left hθθ
  have hθl : unitDir c ^ ℓ = (starRingEnd ℂ (unitDir c) ^ ℓ)⁻¹ := by
    conv_lhs => rw [hθinv]
    exact inv_zpow _ _
  have hcg : starRingEnd ℂ g = -starRingEnd ℂ κ * g * starRingEnd ℂ (unitDir c) := by
    linear_combination (starRingEnd ℂ κ) * hpair - starRingEnd ℂ g * hκκ
  simp only [map_mul, map_zpow₀, Complex.conj_conj, Complex.conj_ofReal]
  rw [hcg, hθl, zpow_sub₀ hφ0, zpow_one, div_eq_mul_inv]
  linear_combination (-(g * starRingEnd ℂ (unitDir c) * (starRingEnd ℂ (unitDir c) ^ ℓ)⁻¹ *
    (Λ : ℂ))) * hκκ

open Classical in
/-- **The reflection of the twists.** If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support of
`Λ`, then `S_β(X; 1 - ℓ) = -κ conj S_β(X; ℓ)` for every `X` and every `ℓ ∈ ℤ`. -/
theorem twistedSum_reflect (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (X : ℕ) (ℓ : ℤ) :
    twistedSum g Λ β X (1 - ℓ) = -κ * starRingEnd ℂ (twistedSum g Λ β X ℓ) := by
  unfold twistedSum
  rw [map_sum, mul_sum]
  exact sum_congr rfl fun c _ => term_reflect (g c) κ hκ c (Λ c) (h12 c) ℓ

/-- **The pairing identities** (first form). Let `k ∈ ℤ` (so that `m = 2k + 1` is odd). If on the
support of `w` the identity `g(c)² = -κ c/|c|` holds and `conj χ₃(c) = χ(c)`, as for
`χ = (ν/c)₄` and `χ₃ = (ν³/c)₄`, then
`∑ conj(χ₃(c)) g(c) (c/|c|)^{-k-1} w(c) = -κ conj (∑ conj(χ(c)) g(c) (c/|c|)^k w(c))`,
that is `A(ν³, -m) = -κ conj A(ν, m)`. -/
theorem twistedAvg_pairing (χ χ₃ g : GaussianInt → ℂ) (w : GaussianInt → ℝ)
    (s : Finset GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (hχ : ∀ c ∈ s, w c ≠ 0 → starRingEnd ℂ (χ₃ c) = χ c)
    (h12 : ∀ c ∈ s, w c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (k : ℤ) :
    twistedAvg χ₃ g w s (-k - 1) = -κ * starRingEnd ℂ (twistedAvg χ g w s k) := by
  unfold twistedAvg
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun c hc => ?_
  by_cases hw : w c = 0
  · simp [hw]
  rcases h12 c hc hw with hg | hg
  · simp [hg]
  by_cases hg0 : g c = 0
  · simp [hg0]
  have hθ0 := unitDir_ne_zero_of hg0 hg
  have hc0 : c ≠ 0 := by rintro rfl; exact hθ0 unitDir_zero
  have hθ := norm_unitDir hc0
  have hpair := mul_conj_eq_neg_conj hθ hκ (Or.inr hg)
  have hκκ := mul_conj_self_eq_one hκ
  have hconjθ : starRingEnd ℂ (unitDir c) = (unitDir c)⁻¹ :=
    eq_inv_of_mul_eq_one_right (mul_conj_self_eq_one hθ)
  -- `conj g = -conj κ · g · conj θ`
  have hcg : starRingEnd ℂ (g c) = -starRingEnd ℂ κ * g c * starRingEnd ℂ (unitDir c) := by
    linear_combination (starRingEnd ℂ κ) * hpair - starRingEnd ℂ (g c) * hκκ
  rw [hχ c hc hw]
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, map_zpow₀]
  rw [hcg, hconjθ, inv_zpow, zpow_sub_one₀ hθ0, zpow_neg]
  linear_combination (-(χ c * g c * ((unitDir c) ^ k)⁻¹ * (unitDir c)⁻¹ * (w c : ℂ))) * hκκ

/-- **Why quartic.** If `|g| = 1` and `g^k = ξ` with `k ≥ 1`, then `ḡ = g^{k-1} ξ̄`. For the quartic
Gauss sum `k = 2`, so conjugation carries a twisted first moment to a twisted first moment; for
`k ≥ 3` it lands on the `(k-1)`-st moment. -/
theorem conj_eq_pow_mul {g ξ : ℂ} {k : ℕ} (hk : 1 ≤ k) (hg : ‖g‖ = 1) (h : g ^ k = ξ) :
    starRingEnd ℂ g = g ^ (k - 1) * starRingEnd ℂ ξ := by
  have hgg := mul_conj_self_eq_one hg
  rw [← h, map_pow]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ (starRingEnd ℂ g) j, ← mul_assoc, ← mul_pow, hgg, one_pow,
    one_mul]

end QuarticPairing
