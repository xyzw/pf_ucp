import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Pointwise Hilbert-space identities for the nonattainment lower bound.
They split a real amplitude from a normalized photon vector, recover its
current, and retain the longitudinal component with the exact metric factor.
-/

namespace GptLean.Nonattainment

open MeasureTheory
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def covariantVector (e : ℝ) (v A : H) : H :=
  (-Complex.I) • v - (e : ℂ) • A

theorem covariant_inner_im_zero {u v A : H} {e : ℝ}
    (horth : (⟪u, v⟫_ℂ).re = 0) (hreal : (⟪u, A⟫_ℂ).im = 0) :
    (⟪u, covariantVector e v A⟫_ℂ).im = 0 := by
  simp only [covariantVector, inner_sub_right, inner_smul_right]
  simp [Complex.mul_im, horth, hreal]

theorem amplitude_covariant_norm_sq (a da : ℝ) {u w : H}
    (hu : ‖u‖ = 1) (hw : (⟪u, w⟫_ℂ).im = 0) :
    ‖((-Complex.I) * (da : ℂ)) • u + (a : ℂ) • w‖ ^ 2 =
      da ^ 2 + a ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ)]
  simp only [norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, hu, mul_one, mul_pow, sq_abs,
    inner_smul_left, inner_smul_right]
  simp [Complex.mul_re, Complex.mul_im, hw]

theorem amplitude_covariant_current (a da : ℝ) {u w : H} (hu : ‖u‖ = 1) :
    (⟪(a : ℂ) • u, ((-Complex.I) * (da : ℂ)) • u + (a : ℂ) • w⟫_ℂ).re =
      a ^ 2 * (⟪u, w⟫_ℂ).re := by
  simp only [inner_smul_left, inner_add_right, inner_smul_right]
  simp [
    inner_self_eq_norm_sq_to_K, hu, Complex.mul_re, Complex.mul_im, pow_two, mul_assoc]

theorem current_centered_norm_sq {u w : H} {c : ℝ}
    (hu : ‖u‖ = 1) (hcurrent : (⟪u, w⟫_ℂ).re = c) :
    ‖w‖ ^ 2 = ‖w - (c : ℂ) • u‖ ^ 2 + c ^ 2 := by
  have hsym : (⟪w, u⟫_ℂ).re = c := by
    exact (inner_re_symm (𝕜 := ℂ) w u).trans hcurrent
  rw [norm_sub_sq (𝕜 := ℂ)]
  simp only [inner_smul_right, RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hsym, norm_smul, Complex.norm_real, Real.norm_eq_abs, hu, mul_one, sq_abs]
  ring

/-- The finite-vector Cauchy--Schwarz estimate retains a tangent component. -/
theorem norm_sum_real_smul_sq_le {I : Type*} [Fintype I] (t : I → ℝ) (v : I → H) :
    ‖∑ i, (t i : ℂ) • v i‖ ^ 2 ≤ (∑ i, t i ^ 2) * (∑ i, ‖v i‖ ^ 2) := by
  have ht : ‖∑ i, (t i : ℂ) • v i‖ ≤ ∑ i, |t i| * ‖v i‖ := by
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs] using
      norm_sum_le (s := Finset.univ) (f := fun i => (t i : ℂ) • v i)
  have hs := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (abs_nonneg _) (norm_nonneg _)))).mpr ht
  exact hs.trans (by simpa only [sq_abs] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |t i|) (fun i => ‖v i‖))

theorem norm_unit_tangent_sq_le {I : Type*} [Fintype I]
    (t : I → ℝ) (v : I → H) (ht : ∑ i, t i ^ 2 = 1) :
    ‖∑ i, (t i : ℂ) • v i‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
  simpa only [ht, one_mul] using norm_sum_real_smul_sq_le t v

/-- The unit-circle longitudinal derivative includes the length and metric
factor. The half-current contributes its exact squared constant. -/
theorem longitudinal_energy_lower {I : Type*} [Fintype I]
    (t : I → ℝ) (v : I → H) {u : H} {J L c : ℝ}
    (ht : ∑ i, t i ^ 2 = 1) (hu : ‖u‖ = 1)
    (hJ : J ≠ 0) (hL : L ≠ 0)
    (hcurrent : (⟪u, ((L * J : ℝ) : ℂ) • (∑ i, (t i : ℂ) • v i)⟫_ℂ).re = c) :
    (‖((L * J : ℝ) : ℂ) • (∑ i, (t i : ℂ) • v i) - (c : ℂ) • u‖ ^ 2 + c ^ 2) /
      (L ^ 2 * J ^ 2) ≤ ∑ i, ‖v i‖ ^ 2 := by
  rw [← current_centered_norm_sq hu hcurrent, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, mul_pow]
  rw [mul_div_cancel_left₀ _ (mul_ne_zero (pow_ne_zero 2 hL) (pow_ne_zero 2 hJ))]
  exact norm_unit_tangent_sq_le t v ht

end GptLean.Nonattainment
