import PfHk.PhysicalLocalEnergySobolev
import PfHk.MultiplierNormAlgebra

/-! Multiplying the proved pointwise Fock-field bound by an arbitrary measurable
scalar coefficient. The multiplication domains and the resulting covariant
estimate are derived, rather than supplied as analytic premises. -/

noncomputable section
namespace PfHk.PhysicalCoordinateMultipliers

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalLocalEnergy
open scoped ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option maxHeartbeats 10000
set_option profiler true

attribute [local irreducible] PhysicalPFReference.field PhysicalPFReference.covariant
  PhysicalPFReference.inclusion PhysicalPFReference.ordinary PhysicalPFReference.radiation
  PhysicalPFReference.radiationSource roughMultiply kernelField
  radiationGraphInclusion radiationGraphDerivative

variable {I : Type} [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i : I, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i : I, ∀ᵐ x : Position I ∂volume, ‖(κ i x).val‖ ≤ M)


end PfHk.PhysicalCoordinateMultipliers
