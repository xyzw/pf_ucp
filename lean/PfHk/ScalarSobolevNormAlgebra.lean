import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-! Conversion between the scalar L^(2p) norm and the Lp norm of its
square, in the exact integral form used by scalar Sobolev estimates. -/

noncomputable section
namespace PfHk.ScalarSobolevNormAlgebra

open MeasureTheory
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 15000

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ} {f : X → ℝ}

theorem square_eLpNorm (hp : 0 < p) :
    eLpNorm (fun x => f x ^ 2) (ENNReal.ofReal p) μ =
      eLpNorm f (ENNReal.ofReal (2 * p)) μ ^ 2 := by
  have hmul : ENNReal.ofReal p * ENNReal.ofReal (2 : ℝ) = ENNReal.ofReal (2 * p) := by
    rw [← ENNReal.ofReal_mul hp.le, mul_comm p 2]
  have h := eLpNorm_norm_rpow (μ := μ) (p := ENNReal.ofReal p) f (by norm_num : (0 : ℝ) < 2)
  simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, hmul, ENNReal.rpow_two] using h

theorem square_memLp (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal (2 * p)) μ) :
    MemLp (fun x => f x ^ 2) (ENNReal.ofReal p) μ := by
  refine ⟨hf.aestronglyMeasurable.pow 2, ?_⟩
  rw [square_eLpNorm hp]
  exact ENNReal.pow_lt_top hf.eLpNorm_lt_top

theorem square_integral_rpow (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal (2 * p)) μ) :
    (∫ x, (f x ^ 2) ^ p ∂μ) ^ (1 / p) =
      (eLpNorm f (ENNReal.ofReal (2 * p)) μ).toReal ^ 2 := by
  have hs := square_memLp hp hf
  have hn := lpNorm_eq_integral_norm_rpow_toReal
    (p := ENNReal.ofReal p) (f := fun x => f x ^ 2)
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top hs.aestronglyMeasurable
  have hi : lpNorm (fun x => f x ^ 2) (ENNReal.ofReal p) μ =
      (∫ x, (f x ^ 2) ^ p ∂μ) ^ (1 / p) := by
    simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs, abs_pow, sq_abs, one_div] using hn
  calc
    _ = (eLpNorm (fun x => f x ^ 2) (ENNReal.ofReal p) μ).toReal :=
      ((toReal_eLpNorm hs.aestronglyMeasurable).trans hi).symm
    _ = (eLpNorm f (ENNReal.ofReal (2 * p)) μ ^ 2).toReal :=
      congrArg ENNReal.toReal (square_eLpNorm hp)
    _ = _ := ENNReal.toReal_pow _ _

end PfHk.ScalarSobolevNormAlgebra
