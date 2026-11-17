import PfHk.DyadicFractional

/-! Pointwise comparison of dyadic endpoint coefficients with the
physical radial densities. These inequalities retain the exponential
at its actual radial argument. -/

noncomputable section
namespace PfHk.DyadicFractional

set_option Elab.async false
set_option maxHeartbeats 80000

theorem coefficient_two_le_radius_sq {τ β R : ℝ} (hτ : 1 ≤ τ) (hβ : β ≤ 1) :
    coefficient τ β R 2 ≤ R ^ 2 := by
  rw [coefficient_two]
  apply (div_le_iff₀ (by linarith : 0 < τ)).mpr
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hβ.trans hτ) (sq_nonneg R)

theorem coefficient_two_le_zero {τ β R : ℝ}
    (hτ : 1 ≤ τ) (hβ : 0 ≤ β) (hR : 0 < R) (hR1 : R ≤ 1) :
    coefficient τ β R 2 ≤ coefficient τ β R 0 := by
  have hR2 : R ^ 2 ≤ 1 := by nlinarith
  have hτ3 : 1 ≤ τ ^ 3 := one_le_pow₀ hτ
  calc
    _ ≤ β := by
      rw [coefficient_two]
      apply (div_le_iff₀ (by linarith : 0 < τ)).mpr
      exact mul_le_mul_of_nonneg_left (hR2.trans hτ) hβ
    _ ≤ _ := by
      rw [coefficient_zero]
      apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
      calc
        _ ≤ β * 1 := mul_le_mul_of_nonneg_left hR2 hβ
        _ ≤ β * τ ^ 3 := mul_le_mul_of_nonneg_left hτ3 hβ
        _ = _ := mul_comm _ _

/-- The zero-order coefficient follows from radius and logarithmic
convexity comparisons on the annulus. -/
theorem coefficient_zero_le_radial {τ β b R r B K : ℝ}
    (hτ : 0 ≤ τ) (hb : 0 ≤ b) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hR : 0 < R) (hr : 0 < r) (hβ : β ≤ B * b) (hscale : r ≤ K * R) :
    coefficient τ β R 0 ≤ (B * K ^ 2) * (τ ^ 3 * b / r ^ 2) := by
  have hsquare : r ^ 2 ≤ K ^ 2 * R ^ 2 := by
    have h := pow_le_pow_left₀ hr.le hscale 2
    simpa only [mul_pow] using h
  have hinv : 1 / R ^ 2 ≤ K ^ 2 / r ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hR) (sq_pos_of_pos hr)).mpr
    simpa only [one_mul] using hsquare
  rw [coefficient_zero]
  calc
    _ ≤ τ ^ 3 * (B * b) / R ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβ (by positivity))
        (sq_nonneg R)
    _ = (B * τ ^ 3 * b) * (1 / R ^ 2) := by ring
    _ ≤ (B * τ ^ 3 * b) * (K ^ 2 / r ^ 2) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

/-- A bounded cutoff can be inserted without changing the coefficient
comparison constant. -/
theorem coefficient_zero_cutoff_le_radial {τ β b R r B K η : ℝ}
    (hτ : 0 < τ) (hβpos : 0 < β) (hb : 0 ≤ b) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hR : 0 < R) (hr : 0 < r) (hβ : β ≤ B * b) (hscale : r ≤ K * R)
    (hη : |η| ≤ 1) :
    coefficient τ β R 0 * η ^ 2 ≤ (B * K ^ 2) * (τ ^ 3 * b / r ^ 2) := by
  have hη2 : η ^ 2 ≤ 1 := by
    have h := abs_le.mp hη
    nlinarith [sq_nonneg η]
  exact (mul_le_of_le_one_right (coefficient_pos hτ hβpos hR 0).le hη2).trans
    (coefficient_zero_le_radial hτ.le hb hB hK hR hr hβ hscale)

end PfHk.DyadicFractional
