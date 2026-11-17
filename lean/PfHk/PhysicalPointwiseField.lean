import GptLean.PhysicalPFReference

/-! The pointwise kernel-field estimate on the actual reference-domain
representatives, using the already constructed radiation graph. -/

noncomputable section
namespace PfHk.PhysicalCoordinateMultipliers

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
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
  have hb : ‖kernelField C (κ i x) (radiationSource I V u x)‖ ≤
      2 * max M 0 * ‖radiationGraphDerivative (radiationSource I V u x)‖ +
        max M 0 * ‖radiationGraphInclusion (radiationSource I V u x)‖ := by
    apply (kernelField_norm_le C (κ i x) (radiationSource I V u x)).trans
    gcongr
    · exact (norm_snd_le (κ i x).val).trans (hk.trans (le_max_left _ _))
    · exact (norm_fst_le (κ i x).val).trans (hk.trans (le_max_left _ _))
  have hl := congrArg (fun z : PhotonFock => ‖z‖) hf
  have hr := congrArg₂ (fun r v : PhotonFock => 2 * max M 0 * ‖r‖ + max M 0 * ‖v‖) hd hj
  exact hl.le.trans (hb.trans_eq hr.symm)

end PfHk.PhysicalCoordinateMultipliers
