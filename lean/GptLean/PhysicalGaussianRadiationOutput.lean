import GptLean.PhysicalPhotonGaussianRadiation
import GptLean.PhysicalHardSpatialRadiation

/-!
The hard Gaussian radiation output is recovered from the actual fiber
operator graph and pulled back through the same photon unitary. This is a
bounded linear map on the full radiation graph. Its norm is exactly the
hard momentum energy, so it supplies the rest term of the spectral source.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory Filter PhysicalGaussianCoordinates PhysicalHardSpatialRadiation
  PhotonLocalizationChannel
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T}
  (normal : NormalTraceData R) (F : NormalFunctionalData R)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (κ : ℝ) {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)

def gaussianRadiationInput : RadiationGraphSpace →L[ℂ] Lp (HardPhotonFock κ) 2 W.space.measure :=
  (photonGaussianUnitary BF κ W).toContinuousLinearEquiv.toContinuousLinearMap.comp
    radiationGraphInclusion

include normal F C in
private theorem gaussianRadiationInput_finite (q : RadiationGraphSpace) :
    finite W.space.measure κ (gaussianRadiationInput BF κ W q) :=
  photonGaussianUnitary_hard_radiation_finite normal F BF C κ W q

include normal F C in
private theorem gaussianRadiationInput_bound (q : RadiationGraphSpace) :
    (∫⁻ ω, radiationForm ((gaussianRadiationInput BF κ W q ω).val) ∂W.space.measure) ≤
      ENNReal.ofReal ((‖hardRadiationRoot κ‖ * ‖q‖) ^ 2) := by
  rw [show (∫⁻ ω, radiationForm ((gaussianRadiationInput BF κ W q ω).val) ∂W.space.measure) =
    ENNReal.ofReal (‖hardRadiationRoot κ q‖ ^ 2) from
      photonGaussianUnitary_hard_radiation normal F BF C κ W q]
  exact ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (norm_nonneg _) ((hardRadiationRoot κ).le_opNorm q) 2)

def gaussianRadiationOutput : RadiationGraphSpace →L[ℂ] Lp (HardPhotonFock κ) 2 W.space.measure :=
  boundedOutput W.space.measure BF κ (gaussianRadiationInput BF κ W)
    (gaussianRadiationInput_finite normal F BF C κ W)
    ‖hardRadiationRoot κ‖ (norm_nonneg (hardRadiationRoot κ))
    (gaussianRadiationInput_bound normal F BF C κ W)

/-- Actual hard radiation output, expressed in the original photon coordinates. -/
def hardGaussianRoot : RadiationGraphSpace →L[ℂ] PhotonFock :=
  (photonGaussianUnitary BF κ W).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (gaussianRadiationOutput normal F BF C κ W)

theorem hardGaussianRoot_unitary (q : RadiationGraphSpace) :
    photonGaussianUnitary BF κ W (hardGaussianRoot normal F BF C κ W q) =
      gaussianRadiationOutput normal F BF C κ W q :=
  (photonGaussianUnitary BF κ W).apply_symm_apply _

theorem hardGaussianRoot_graph (q : RadiationGraphSpace) :
    ∀ᵐ ω ∂W.space.measure,
      (photonGaussianUnitary BF κ W (radiationGraphInclusion q) ω,
        photonGaussianUnitary BF κ W (hardGaussianRoot normal F BF C κ W q) ω) ∈
          (hardRadiationOperator κ).graph := by
  have hgraph := boundedOutput_graph W.space.measure BF κ (gaussianRadiationInput BF κ W)
    (gaussianRadiationInput_finite normal F BF C κ W)
    ‖hardRadiationRoot κ‖ (norm_nonneg (hardRadiationRoot κ))
    (gaussianRadiationInput_bound normal F BF C κ W) q
  exact (congrArg (fun w : Lp (HardPhotonFock κ) 2 W.space.measure =>
    ∀ᵐ ω ∂W.space.measure,
      (photonGaussianUnitary BF κ W (radiationGraphInclusion q) ω, w ω) ∈
        (hardRadiationOperator κ).graph)
    (hardGaussianRoot_unitary normal F BF C κ W q)).mpr hgraph

theorem hardGaussianRoot_norm_sq (q : RadiationGraphSpace) :
    ‖hardGaussianRoot normal F BF C κ W q‖ ^ 2 = ‖hardRadiationRoot κ q‖ ^ 2 := by
  have h := boundedOutput_norm_sq W.space.measure BF κ (gaussianRadiationInput BF κ W)
    (gaussianRadiationInput_finite normal F BF C κ W)
    ‖hardRadiationRoot κ‖ (norm_nonneg (hardRadiationRoot κ))
    (gaussianRadiationInput_bound normal F BF C κ W) q
  have he := h.trans (photonGaussianUnitary_hard_radiation normal F BF C κ W q)
  change ENNReal.ofReal (‖gaussianRadiationOutput normal F BF C κ W q‖ ^ 2) = _ at he
  have hn : ‖hardGaussianRoot normal F BF C κ W q‖ =
      ‖gaussianRadiationOutput normal F BF C κ W q‖ :=
    (photonGaussianUnitary BF κ W).symm.norm_map _
  rw [hn]
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp he

theorem hardGaussianRoot_spatial_norm_sq {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (q : SpatialRadiationGraph ν) :
    ‖(hardGaussianRoot normal F BF C κ W).compLpL 2 ν q‖ ^ 2 =
      ‖(hardRadiationRoot κ).compLpL 2 ν q‖ ^ 2 := by
  have h : (fun x => ‖(hardGaussianRoot normal F BF C κ W).compLpL 2 ν q x‖ ^ 2) =ᵐ[ν]
      fun x => ‖(hardRadiationRoot κ).compLpL 2 ν q x‖ ^ 2 := by
    filter_upwards [(hardGaussianRoot normal F BF C κ W).coeFn_compLpL q,
      (hardRadiationRoot κ).coeFn_compLpL q] with x hq hr
    exact (congrArg (fun v : PhotonFock => ‖v‖ ^ 2) hq).trans
      ((hardGaussianRoot_norm_sq normal F BF C κ W (q x)).trans
        (congrArg (fun v : PhotonFock => ‖v‖ ^ 2) hr).symm)
  exact (ENNReal.ofReal_eq_ofReal_iff
    (sq_nonneg ‖(hardGaussianRoot normal F BF C κ W).compLpL 2 ν q‖)
    (sq_nonneg ‖(hardRadiationRoot κ).compLpL 2 ν q‖)).mp
    ((lp_square_lintegral ((hardGaussianRoot normal F BF C κ W).compLpL 2 ν q)).symm.trans
      ((lintegral_congr_ae (h.mono fun _ hx => congrArg ENNReal.ofReal hx)).trans
        (lp_square_lintegral ((hardRadiationRoot κ).compLpL 2 ν q))))

end GptLean.PhysicalFock
