import PfHk.ScalarLpDecomposition
import GptLean.Repair.TraceChannel

/-! Square-root amplitudes of scalar coefficients. These are elementary
Lp identities, independent of every Hamiltonian and Carleman weight. -/

noncomputable section
namespace PfHk.ScalarSqrtLp

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def amplitude (c : X → ℝ) (x : X) : ℝ := Real.sqrt |c x|

omit [MeasurableSpace X] in
theorem amplitude_sq (c : X → ℝ) (x : X) : amplitude c x ^ 2 = |c x| :=
  Real.sq_sqrt (abs_nonneg _)

theorem amplitude_memLp {c : X → ℝ} (hc : MemLp c (3 / 2) μ) :
    MemLp (amplitude c) 3 μ := by
  have h := hc.norm_rpow_div (1 / 2)
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
  have he : (3 / 2 : ℝ≥0∞) / (1 / 2) = 3 := by
    simp only [div_eq_mul_inv, one_mul, inv_inv, mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞), mul_one]
  rw [he] at h
  change MemLp (fun x => Real.sqrt |c x|) 3 μ
  simpa only [← Real.sqrt_eq_rpow, Real.norm_eq_abs] using h

theorem amplitude_norm_sq (c : X → ℝ) :
    (eLpNorm (amplitude c) 3 μ).toReal ^ 2 = (eLpNorm c (3 / 2) μ).toReal := by
  have h := eLpNorm_norm_rpow (p := (3 : ℝ≥0∞)) (μ := μ) c
    (by norm_num : (0 : ℝ) < 1 / 2)
  have he : (3 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 3 / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat, div_eq_mul_inv, one_mul]
  rw [he] at h
  have ht := congrArg ENNReal.toReal h
  simp only [← ENNReal.toReal_rpow, Real.norm_eq_abs, ← Real.sqrt_eq_rpow] at ht
  exact (congrArg (fun r : ℝ => r ^ 2) ht).trans (Real.sq_sqrt ENNReal.toReal_nonneg)

theorem amplitude_measurable {c : X → ℝ} (hc : AEStronglyMeasurable c μ) :
    AEStronglyMeasurable (amplitude c) μ := Real.continuous_sqrt.comp_aestronglyMeasurable hc.norm

end PfHk.ScalarSqrtLp
