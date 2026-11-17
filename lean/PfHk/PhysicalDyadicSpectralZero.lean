import PfHk.PhysicalDyadicSpectral

/-! The order-zero spectral squared norm is the actual L2 squared norm. -/

noncomputable section
namespace PfHk.PhysicalDyadicIntegralFractional

open GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PhysicalOperatorDomain

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

attribute [local irreducible] PhysicalPFReference.inclusion

variable {I : Type} [Fintype I] [DecidableEq I]

theorem fractionalNormSq_zero (spectral : ComparisonSpectralCalculus (I := I))
    (u : Reference I (fun _ => 0)) (hu : ComparisonDomain (fun _ => 0) u) :
    fractionalNormSq spectral 0 u hu = ‖inclusion I (fun _ => 0) u‖ ^ 2 :=
  congrArg (fun w : WaveSpace I => ‖w‖ ^ 2) (spectral.fractional_zero u hu)

end PfHk.PhysicalDyadicIntegralFractional
