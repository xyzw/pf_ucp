import PfHk.PhysicalLocalEnergyRough
import PfHk.RoughFieldMultiplierAlgebra
import PfHk.PhysicalPointwiseField

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
set_option maxHeartbeats 30000

attribute [local irreducible] PhysicalPFReference.field PhysicalPFReference.covariant
  PhysicalPFReference.inclusion PhysicalPFReference.ordinary PhysicalPFReference.radiation
  PhysicalPFReference.radiationSource kernelField
  radiationGraphInclusion radiationGraphDerivative

variable {I : Type} [Fintype I] [DecidableEq I]
variable (V : Position I → ℝ)
variable (C : CanonicalSectorCCR photonMeasure)
variable (κ : I → Position I → WeightedPhotonKernel)
variable (hκ : ∀ i : I, AEStronglyMeasurable (κ i) volume)
variable (M : ℝ)
variable (hbound : ∀ i : I, ∀ᵐ x : Position I ∂volume, ‖(κ i x).val‖ ≤ M)

theorem field_multiplier (b : Position I → ℝ) (hb : AEStronglyMeasurable b volume)
    (u : Reference I V) (i : I)
    (hR : HasMultiplier b (radiation I V u))
    (hJ : HasMultiplier b (inclusion I V u)) :
    ∃ hF : HasMultiplier b (field I V C κ hκ M hbound i u),
      ‖roughMultiply b (field I V C κ hκ M hbound i u) hF‖ ^ 2 ≤
        8 * (max M 0) ^ 2 * ‖roughMultiply b (radiation I V u) hR‖ ^ 2 +
        2 * (max M 0) ^ 2 * ‖roughMultiply b (inclusion I V u) hJ‖ ^ 2 := by
  exact RoughFieldMultiplierAlgebra.field_multiplier (H := PhotonFock)
    b hb (max M 0) (field I V C κ hκ M hbound i u) (radiation I V u) (inclusion I V u)
    (field_norm_ae V C κ hκ M hbound u i) hR hJ

theorem covariant_multiplier (b : Position I → ℝ) (hb : AEStronglyMeasurable b volume)
    (e : ℝ) (u : Reference I V) (i : I)
    (hP : HasMultiplier b (ordinary I V i u))
    (hR : HasMultiplier b (radiation I V u))
    (hJ : HasMultiplier b (inclusion I V u)) :
    ∃ hD : HasMultiplier b (covariant I V C κ hκ M hbound e i u),
      ‖roughMultiply b (covariant I V C κ hκ M hbound e i u) hD‖ ^ 2 ≤
        2 * ‖roughMultiply b (ordinary I V i u) hP‖ ^ 2 +
        16 * e ^ 2 * (max M 0) ^ 2 * ‖roughMultiply b (radiation I V u) hR‖ ^ 2 +
        4 * e ^ 2 * (max M 0) ^ 2 * ‖roughMultiply b (inclusion I V u) hJ‖ ^ 2 := by
  exact RoughFieldMultiplierAlgebra.covariant_multiplier (H := PhotonFock)
    b hb e (max M 0) (ordinary I V i u) (field I V C κ hκ M hbound i u)
    (radiation I V u) (inclusion I V u) (covariant I V C κ hκ M hbound e i u)
    (covariant_apply I V C κ hκ M hbound e i u)
    (field_norm_ae V C κ hκ M hbound u i) hP hR hJ

end PfHk.PhysicalCoordinateMultipliers
