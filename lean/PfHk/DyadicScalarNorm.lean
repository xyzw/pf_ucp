import PfHk.L2ScalarNorm

noncomputable section
namespace PfHk.DyadicScalarNorm

open MeasureTheory GptLean GptLean.ElectronicH1Multiplier GptLean.ElectronicH1Space
  PfHk.PhysicalCutoffCommutator

set_option Elab.async false
set_option maxHeartbeats 10000

variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem multiplier_norm_sq_ae (a : DifferentiableMultiplier I) (u : L2 H I) :
    (fun x => ‖a.multiplier u x‖ ^ 2) =ᵐ[volume]
      fun x => a.weight x ^ 2 * ‖u x‖ ^ 2 := by
  filter_upwards [scalar_multiplier_ae a u] with x hx
  rw [hx, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem multiplier_product_norm_sq_ae (a : DifferentiableMultiplier I)
    (η E : EuclideanSpace ℝ I → ℝ) (u : L2 H I)
    (hw : ∀ x, a.weight x = η x * E x) :
    (fun x => ‖a.multiplier u x‖ ^ 2) =ᵐ[volume]
      fun x => η x ^ 2 * E x ^ 2 * ‖u x‖ ^ 2 := by
  apply (multiplier_norm_sq_ae a u).trans
  exact ae_of_all _ fun x => by
    dsimp only
    rw [hw x, mul_pow]

end PfHk.DyadicScalarNorm
