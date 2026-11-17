import GptLean.PhysicalFockSoftRadiation
import GptLean.PhysicalFockSpatialField
import GptLean.PhysicalPhotonMarginalMoments
import GptLean.PhysicalPFSource

/-!
The soft-energy quantity removed by Gaussian slicing is the expectation of
the actual soft momentum form of the original normal state. Both the
rank-one identity and the spectral series use the same spatial radiation
graph and its constructed soft square root.
-/

noncomputable section
namespace GptLean.PhysicalPhotonMarginal

open MeasureTheory Filter PhysicalFock PhysicalNormalTrace PhysicalPFReference
open PhysicalClosedForms PhysicalPFSource
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

private theorem lintegral_l2_norm_sq {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure X) (u : Lp H 2 μ) :
    (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ) = ENNReal.ofReal (‖u‖ ^ 2) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  exact (ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u))
    (ae_of_all μ fun x => sq_nonneg ‖u x‖)).symm.trans
      (congrArg ENNReal.ofReal (PhotonKernelLocalization.l2_norm_sq_eq_integral u).symm)

variable (B : StandardNormalTraceBackground) {X : Type} [MeasurableSpace X]
  (μ : Measure X) [IsSeparable μ] (κ : ℝ)

attribute [local irreducible] fullMomentumForm RemovalState.PositiveForm.expectation
  photonMoment softRadiationRoot radiationGraphInclusion

set_option maxHeartbeats 800000 in
/-- Exact soft momentum expectation of an actual spatial graph vector. -/
theorem fullSoftForm_graph (q : SpatialRadiationGraph μ) :
    (fullMomentumForm B μ (NormalPhoton.softWeight κ) (NormalPhoton.softWeight_measurable κ)).expectation
      ((B.realization (SpatialPhotonSpace μ)).rank.rankOne (spatialRadiationInclusion μ q)) =
        ENNReal.ofReal (‖(softRadiationRoot κ).compLpL 2 μ q‖ ^ 2) := by
  refine (fullMomentumForm_rankOne B μ (NormalPhoton.softWeight κ)
    (NormalPhoton.softWeight_measurable κ) (spatialRadiationInclusion μ q)).trans ?_
  have he : (fun x => photonMoment (NormalPhoton.softWeight κ)
      (spatialRadiationInclusion μ q x)) =ᵐ[μ]
      fun x => ENNReal.ofReal (‖(softRadiationRoot κ).compLpL 2 μ q x‖ ^ 2) := by
    filter_upwards [radiationGraphInclusion.coeFn_compLpL q,
      (softRadiationRoot κ).coeFn_compLpL q] with x hi hr
    exact (congrArg (photonMoment (NormalPhoton.softWeight κ)) hi).trans
      ((softRadiationRoot_energy κ (q x)).trans
        (congrArg (fun u : PhotonFock => ENNReal.ofReal (‖u‖ ^ 2)) hr.symm))
  exact (lintegral_congr_ae he).trans
    (lintegral_l2_norm_sq μ ((softRadiationRoot κ).compLpL 2 μ q))

/-- Positive spectral summation preserves the exact soft-root identity. -/
theorem fullSoftForm_source (q : ℕ → SpatialRadiationGraph μ)
    {x : B.Trace (SpatialPhotonSpace μ)}
    (hq : HasSum (fun n => (B.realization (SpatialPhotonSpace μ)).rank.rankOne
      (spatialRadiationInclusion μ (q n))) x)
    (hs : Summable (fun n => ‖(softRadiationRoot κ).compLpL 2 μ (q n)‖ ^ 2)) :
    (fullMomentumForm B μ (NormalPhoton.softWeight κ) (NormalPhoton.softWeight_measurable κ)).expectation x =
      ENNReal.ofReal (∑' n, ‖(softRadiationRoot κ).compLpL 2 μ (q n)‖ ^ 2) := by
  refine (fullMomentumForm_source B μ (NormalPhoton.softWeight κ)
    (NormalPhoton.softWeight_measurable κ) hq).trans ?_
  calc
    _ = ∑' n, ENNReal.ofReal (‖(softRadiationRoot κ).compLpL 2 μ (q n)‖ ^ 2) := by
      apply tsum_congr
      intro n
      exact (fullMomentumForm_rankOne B μ (NormalPhoton.softWeight κ)
        (NormalPhoton.softWeight_measurable κ) (spatialRadiationInclusion μ (q n))).symm.trans
          (fullSoftForm_graph B μ κ (q n))
    _ = _ := (ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hs).symm

end GptLean.PhysicalPhotonMarginal

namespace GptLean.PhysicalPFSource

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace PhysicalClosedForms
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (k : I → Position I → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (M : ℝ) (hb : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e κ : ℝ)

def softReference : Reference I V →L[ℂ] WaveSpace I :=
  ((softRadiationRoot κ).compLpL 2 volume).comp (radiationSource I V)

theorem Source.soft_expectation {x : B.Trace (WaveSpace I)} (s : Source I V B x)
    (he : (normalEnergy I V C k hk M hb B S e).expectation x < ⊤) :
    (PhysicalPhotonMarginal.fullMomentumForm B (volume : Measure (Position I))
      (NormalPhoton.softWeight κ) (NormalPhoton.softWeight_measurable κ)).expectation x =
        ENNReal.ofReal (∑' n, ‖softReference I V κ (s.vector n)‖ ^ 2) := by
  apply PhysicalPhotonMarginal.fullSoftForm_source B volume κ
    (fun n => radiationSource I V (s.vector n))
  · exact s.hasSum.congr_fun (fun n => congrArg (B.realization (WaveSpace I)).rank.rankOne
      (radiation_matches I V (s.vector n)))
  · exact s.operator_summable C k hk M hb S e he (softReference I V κ)

end GptLean.PhysicalPFSource
