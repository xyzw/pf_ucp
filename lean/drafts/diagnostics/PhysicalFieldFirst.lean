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
variable (V : Position I → ℝ)
variable (C : CanonicalSectorCCR photonMeasure)
variable (κ : I → Position I → WeightedPhotonKernel)
variable (hκ : ∀ i : I, AEStronglyMeasurable (κ i) volume)
variable (M : ℝ)
variable (hbound : ∀ i : I, ∀ᵐ x : Position I ∂volume, ‖(κ i x).val‖ ≤ M)

theorem field_norm_ae (u : Reference I V) (i : I) :
    ∀ᵐ x : Position I ∂volume, ‖field I V C κ hκ M hbound i u x‖ ≤
      2 * max M 0 * ‖radiation I V u x‖ + max M 0 * ‖inclusion I V u x‖ := by
  have hF : (field I V C κ hκ M hbound i u : Position I → PhotonFock) =ᵐ[volume]
      fun x => kernelField C (κ i x) (radiationSource I V u x) := by
    have hc : field I V C κ hκ M hbound i u =
        spatialField volume C (κ i) (hκ i) M (hbound i) (radiationSource I V u) := by
      unfold PhysicalPFReference.field
      rfl
    exact (Filter.EventuallyEq.of_eq (congrArg (fun f : WaveSpace I => ⇑f) hc)).trans
      (spatialField_ae volume C (κ i) (hκ i) M (hbound i) (radiationSource I V u))
  have hJ : (inclusion I V u : Position I → PhotonFock) =ᵐ[volume]
      fun x => radiationGraphInclusion (radiationSource I V u x) :=
    (Filter.EventuallyEq.of_eq (congrArg (fun f : WaveSpace I => ⇑f)
      (radiation_matches I V u).symm)).trans
        (radiationGraphInclusion.coeFn_compLpL (radiationSource I V u))
  have hD : (radiation I V u : Position I → PhotonFock) =ᵐ[volume]
      fun x => radiationGraphDerivative (radiationSource I V u x) := by
    filter_upwards [radiation_graph I V u, hJ] with x hx hj
    exact radiationRoot.mem_graph_snd_inj hx (radiationGraph_pair (radiationSource I V u x)) hj
  filter_upwards [hF, hD, hJ, hbound i] with x hf hd hj hk
  rw [hf, hd, hj]
  apply (kernelField_norm_le C (κ i x) (radiationSource I V u x)).trans
  gcongr
  · exact (norm_snd_le (κ i x).val).trans (hk.trans (le_max_left _ _))
  · exact (norm_fst_le (κ i x).val).trans (hk.trans (le_max_left _ _))


end PfHk.PhysicalCoordinateMultipliers
