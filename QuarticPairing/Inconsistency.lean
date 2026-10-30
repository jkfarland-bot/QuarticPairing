module

public import QuarticPairing.Pairing

@[expose] public section

/-!
# Conjecture 1.2 is inconsistent with the identity (1.2)

* `eq_zero_of_isBigO`: a term `b X^{3/4}` that is `O(X^{5/8})` has `b = 0`.
* `not_conjecture12`: if `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support of `Λ`, Conjecture 1.2
  fails for the class `β`.
* `not_conjecture12_of_defect`: the same conclusion when the identity is assumed only off an
  exceptional set `E` whose weight `∑ |g̃(c)| |Λ(c)|` is `O(X^{1/2+ε})` for every `ε > 0`. For the
  quartic Gauss sum the identity holds at every primary prime and `g̃ = 0` at higher prime powers, so
  `not_conjecture12` applies directly; this version is for use when the identity is known only at
  the primes of degree one.
-/

open Complex Filter Asymptotics Finset

noncomputable section

namespace QuarticPairing

/-- A term `b X^{3/4}` that is `O(X^{5/8})` along the integers has `b = 0`. -/
theorem eq_zero_of_isBigO {b : ℂ}
    (h : (fun X : ℕ => b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[atTop]
      (fun X : ℕ => (X : ℝ) ^ ((5 : ℝ) / 8))) : b = 0 := by
  by_contra hb
  obtain ⟨C, hC⟩ := h.bound
  have hb0 : 0 < ‖b‖ := norm_pos_iff.2 hb
  have ht : Tendsto (fun X : ℕ => ((X : ℝ) ^ ((1 : ℝ) / 8))) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := (hC.and ((ht.eventually_gt_atTop (C / ‖b‖)).and
    (eventually_gt_atTop 0))).exists_forall_of_atTop
  obtain ⟨h1, h2, h3⟩ := hN N le_rfl
  have hX : (0 : ℝ) < N := by exact_mod_cast h3
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hX _), abs_of_pos (Real.rpow_pos_of_pos hX _)] at h1
  have hsplit : (N : ℝ) ^ ((3 : ℝ) / 4) = (N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((5 : ℝ) / 8) := by
    rw [← Real.rpow_add hX]; norm_num
  rw [hsplit] at h1
  have h58 : 0 < (N : ℝ) ^ ((5 : ℝ) / 8) := Real.rpow_pos_of_pos hX _
  have : C < ‖b‖ * (N : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [div_lt_iff₀ hb0] at h2; linarith
  nlinarith

/-- The conclusion from the cases `ℓ = 0` and `ℓ = 1`, given that `S_β(X; 0)` is `O(X^{5/8})`. -/
lemma not_conjecture12_aux (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    (hS : (fun X : ℕ => ‖twistedSum g Λ β X 1‖) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((5 : ℝ) / 8)) →
      (fun X : ℕ => twistedSum g Λ β X 0) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((5 : ℝ) / 8))) :
    ¬ Conjecture12 g Λ β := by
  rintro ⟨b, hb, hconj⟩
  have hε : (0 : ℝ) < 1 / 8 := by norm_num
  have h0 := hconj (1 / 8) hε 0
  have h1 := hconj (1 / 8) hε 1
  simp only [ite_true, one_ne_zero, ite_false, sub_zero] at h0 h1
  have he : (1 : ℝ) / 2 + 1 / 8 = 5 / 8 := by norm_num
  rw [he] at h0 h1
  exact hb (eq_zero_of_isBigO (((hS h1.norm_left).sub h0).congr_left fun X => by ring))

/-- **Conjecture 1.2 of David, Dunn, Hamieh and Lin is inconsistent with their identity (1.2).**
If `g̃(c)² = -κ c/|c|` (or `g̃(c) = 0`) on the support of `Λ`, for a fixed unit `κ`, then the
cases `ℓ = 0` and `ℓ = 1` of the conjecture force `b_β = 0`, which the conjecture excludes. -/
theorem not_conjecture12 (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) {κ : ℂ}
    (hκ : ‖κ‖ = 1) (h12 : ∀ c, Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) :
    ¬ Conjecture12 g Λ β := by
  refine not_conjecture12_aux g Λ β fun h1 => IsBigO.of_norm_left ?_
  have : (fun X : ℕ => ‖twistedSum g Λ β X 0‖) = fun X => ‖twistedSum g Λ β X 1‖ := by
    funext X
    rw [twistedSum_one g Λ β hκ h12 X, norm_mul, norm_neg, hκ, one_mul, Complex.norm_conj]
  rw [this]; exact h1

/-- **The same with an exceptional set.** If the identity holds off a set `E` whose weight
`∑_{c ∈ E, N(c) ≤ X, c ≡ β} |g(c)| |Λ(c)|` is `O(X^{1/2+ε})` for every `ε > 0`, Conjecture 1.2
fails for the class `β`. -/
theorem not_conjecture12_of_defect (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c)
    (hE : ∀ ε : ℝ, 0 < ε →
      (fun X : ℕ => defectSum g Λ β E X) =O[atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    ¬ Conjecture12 g Λ β := by
  refine not_conjecture12_aux g Λ β fun h1 => ?_
  have hD := hE (1 / 8) (by norm_num)
  rw [show (1 : ℝ) / 2 + 1 / 8 = 5 / 8 by norm_num] at hD
  have hsum : (fun X : ℕ => ‖twistedSum g Λ β X 1‖ + 2 * defectSum g Λ β E X) =O[atTop]
      (fun X : ℕ => (X : ℝ) ^ ((5 : ℝ) / 8)) := h1.add (hD.const_mul_left 2)
  refine IsBigO.trans (IsBigO.of_bound 1 (Eventually.of_forall fun X => ?_)) hsum
  have hb := twistedSum_one_sub g Λ β hκ E h12 X
  have hD0 : 0 ≤ defectSum g Λ β E X :=
    sum_nonneg fun c _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hn : ‖twistedSum g Λ β X 0‖ = ‖κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖ := by
    rw [norm_mul, hκ, one_mul, Complex.norm_conj]
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hn]
  calc ‖κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖
      = ‖(twistedSum g Λ β X 1 + κ * starRingEnd ℂ (twistedSum g Λ β X 0)) -
          twistedSum g Λ β X 1‖ := by ring_nf
    _ ≤ ‖twistedSum g Λ β X 1 + κ * starRingEnd ℂ (twistedSum g Λ β X 0)‖ +
          ‖twistedSum g Λ β X 1‖ := norm_sub_le _ _
    _ ≤ ‖twistedSum g Λ β X 1‖ + 2 * defectSum g Λ β E X := by linarith

end QuarticPairing
