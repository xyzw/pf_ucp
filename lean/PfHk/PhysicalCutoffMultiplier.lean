import GptLean.ElectronicH1DifferentiableMultiplier

/-! Scalar cutoffs with bounded second derivatives on the actual PF reference domain. -/

noncomputable section
namespace PfHk.PhysicalCutoffCommutator

open MeasureTheory GptLean
open GptLean.ElectronicH1Multiplier GptLean.ElectronicH1Space
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 10000
set_option Elab.async false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Scalar regularity needed for a second-order cutoff product rule. -/
structure TwiceDifferentiableMultiplier (I : Type) [Fintype I] [DecidableEq I] where
  scalar : DifferentiableMultiplier I
  derivative : I → DifferentiableMultiplier I
  derivative_weight : ∀ i, (derivative i).weight = scalar.gradient i

theorem derivative_multiplier {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (a : TwiceDifferentiableMultiplier I) (i : I)
    (u : L2 H I) :
    (a.derivative i).multiplier u = a.scalar.derivativeMultiplier i u := by
  unfold DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier
  apply Lp.ext
  filter_upwards [
    PhotonLocalization.realL2Multiplier_apply (a.derivative i).weight
      (a.derivative i).differentiable.continuous.aestronglyMeasurable
      (a.derivative i).bound (ae_of_all _ (a.derivative i).bounded) u,
    PhotonLocalization.realL2Multiplier_apply (a.scalar.gradient i)
      (a.scalar.gradient_measurable i).aestronglyMeasurable a.scalar.derivativeBound
      (ae_of_all _ (a.scalar.derivative_bounded i)) u] with x hx hy
  rw [hx, hy, a.derivative_weight]

theorem l2_inner_eq_of_ae {X H : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v w z : Lp H 2 μ)
    (h : ∀ᵐ x ∂μ, ⟪u x, v x⟫_ℂ = ⟪w x, z x⟫_ℂ) :
    ⟪u, v⟫_ℂ = ⟪w, z⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  exact integral_congr_ae h

theorem l2_real_multiplier_pair {X H : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (f : X → ℝ) (u v fu fv : Lp H 2 μ)
    (hu : fu =ᵐ[μ] fun x => f x • u x) (hv : fv =ᵐ[μ] fun x => f x • v x) :
    ⟪u, fv⟫_ℂ = ⟪fu, v⟫_ℂ := by
  apply l2_inner_eq_of_ae
  filter_upwards [hu, hv] with x hx hy
  rw [hx, hy, inner_smul_left_eq_smul, inner_smul_right_eq_smul]


end PfHk.PhysicalCutoffCommutator
