import PfHk.PhysicalCutoffMultiplier

noncomputable section
namespace PfHk.PhysicalCutoffCommutator

open MeasureTheory GptLean GptLean.ElectronicH1Multiplier GptLean.ElectronicH1Space

set_option maxHeartbeats 10000
set_option Elab.async false

theorem scalar_multiplier_ae {I H : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : DifferentiableMultiplier I) (u : L2 H I) :
    a.multiplier u =ᵐ[volume] fun x => a.weight x • u x :=
  PhotonLocalization.realL2Multiplier_apply a.weight
    a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded) u

theorem scalar_multiplier_supported {I H : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : DifferentiableMultiplier I) (u : L2 H I) {s : Set (EuclideanSpace ℝ I)}
    (hs : ∀ x, x ∉ s → a.weight x = 0) :
    ∀ᵐ x ∂volume, x ∉ s → a.multiplier u x = 0 := by
  filter_upwards [scalar_multiplier_ae a u] with x hx
  intro hxs
  rw [hx, hs x hxs, zero_smul]

theorem scalar_multiplier_norm_sq_ae {I H : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : DifferentiableMultiplier I) (ha : ∀ x, 0 ≤ a.weight x) (u : L2 H I) :
    (fun x => ‖a.multiplier u x‖ ^ 2) =ᵐ[volume]
      fun x => (a.weight x * ‖u x‖) ^ 2 := by
  unfold DifferentiableMultiplier.multiplier
  filter_upwards [PhotonLocalization.realL2Multiplier_apply a.weight
    a.differentiable.continuous.aestronglyMeasurable a.bound
    (ae_of_all _ a.bounded) u] with x hx
  rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha x)]

end PfHk.PhysicalCutoffCommutator
