import GptLean.PhysicalFockRadiationCutoff
import GptLean.PhysicalFockSpatialField
import GptLean.PhysicalPhotonMarginalMoments

/-!
The finite radiation form on spatial L2 has exactly the actual spatial
radiation graph as its domain. Bounded energy cutoffs give measurable
graph-valued representatives, so no domain realization is assumed.
-/

noncomputable section

namespace GptLean.PhysicalSpatialRadiationDomain

open MeasureTheory Filter Topology PhysicalFock PhysicalPhotonMarginal PhysicalNormalTrace
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

private def graphValue (v : PhotonFock) : RadiationGraphSpace := by
  classical
  exact if h : v ∈ radiationRoot.domain then
    ⟨(v, radiationRoot ⟨v, h⟩), radiationRoot.mem_graph ⟨v, h⟩⟩ else 0

private theorem graphValue_inclusion (v : PhotonFock) (h : v ∈ radiationRoot.domain) :
    radiationGraphInclusion (graphValue v) = v := by simp [graphValue, h, radiationGraphInclusion]

private theorem graphValue_energy (v : PhotonFock) (h : v ∈ radiationRoot.domain) :
    ENNReal.ofReal (‖radiationGraphDerivative (graphValue v)‖ ^ 2) = radiationForm v := by
  simpa only [graphValue, dite_eq_left h, radiationGraphDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', Submodule.subtypeL_apply] using (radiationRoot_energy ⟨v, h⟩).symm

private theorem graph_norm_sq_le (q : RadiationGraphSpace) :
    ‖q‖ ^ 2 ≤ ‖radiationGraphInclusion q‖ ^ 2 + ‖radiationGraphDerivative q‖ ^ 2 := by
  change (max ‖q.val.1‖ ‖q.val.2‖) ^ 2 ≤ ‖q.val.1‖ ^ 2 + ‖q.val.2‖ ^ 2
  rcases le_total ‖q.val.1‖ ‖q.val.2‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖q.val.1‖]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg ‖q.val.2‖]

private theorem graphValue_bound (v : PhotonFock) :
    ENNReal.ofReal (‖graphValue v‖ ^ 2) ≤ ENNReal.ofReal (‖v‖ ^ 2) + radiationForm v := by
  by_cases h : v ∈ radiationRoot.domain
  · exact (ENNReal.ofReal_le_ofReal (graph_norm_sq_le (graphValue v))).trans_eq (by
      rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        graphValue_inclusion v h, graphValue_energy v h])
  · simp only [graphValue, dite_eq_right h, norm_zero, zero_pow (by decide : 2 ≠ 0),
      ENNReal.ofReal_zero, zero_le]

section Spatial

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem radiationForm_aemeasurable {u : X → PhotonFock}
    (hu : AEStronglyMeasurable u μ) : AEMeasurable (fun x => radiationForm (u x)) μ := by
  let q : PhotonMode → ℝ≥0∞ := fun p => ENNReal.ofReal ‖p.1‖
  have hq : Measurable q := measurable_fst.norm.ennreal_ofReal
  have hm (M : ℕ) : AEMeasurable (fun x => ENNReal.ofReal
      (⟪u x, (cappedWeight q hq M).operator (Nat.cast_nonneg M) (u x)⟫_ℂ).re) μ :=
    (Complex.continuous_re.comp_aestronglyMeasurable (hu.inner
      (((cappedWeight q hq M).operator (Nat.cast_nonneg M)).continuous.comp_aestronglyMeasurable
        hu))).aemeasurable.ennreal_ofReal
  apply (AEMeasurable.iSup hm).congr
  exact ae_of_all μ fun x => (cappedWeight_recovery q hq (u x)).trans
    (photonMoment_frequency (u x))

private theorem graphValue_aestronglyMeasurable (u : Lp PhotonFock 2 μ)
    (hfinite : ∫⁻ x, radiationForm (u x) ∂μ < ⊤) :
    AEStronglyMeasurable (fun x => graphValue (u x)) μ := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun M => (radiationEnergyCutoff M).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u))
  filter_upwards [ae_lt_top' (radiationForm_aemeasurable (Lp.aestronglyMeasurable u)) hfinite.ne]
    with x hx
  have hd := (radiationRoot_domain_iff_finite (u x)).mpr hx
  simpa only [graphValue_inclusion (u x) hd] using
    radiationEnergyCutoff_tendsto (graphValue (u x))

private theorem enorm_rpow_two {E : Type*} [NormedAddCommGroup E] (v : E) :
    ‖v‖ₑ ^ (2 : ℝ≥0∞).toReal = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [ENNReal.toReal_ofNat, ENNReal.rpow_two, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _)]

private theorem graphValue_memLp (u : Lp PhotonFock 2 μ)
    (hfinite : ∫⁻ x, radiationForm (u x) ∂μ < ⊤) :
    MemLp (fun x => graphValue (u x)) 2 μ := by
  refine ⟨graphValue_aestronglyMeasurable u hfinite,
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mpr ?_⟩
  have hu : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ < ⊤ := by
    simpa only [enorm_rpow_two] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (Lp.memLp u).eLpNorm_lt_top
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) + radiationForm (u x) ∂μ :=
      lintegral_mono fun x => (enorm_rpow_two (graphValue (u x))).le.trans (graphValue_bound (u x))
    _ = (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ) + ∫⁻ x, radiationForm (u x) ∂μ :=
      lintegral_add_left' ((Lp.aestronglyMeasurable u).norm.pow 2).aemeasurable.ennreal_ofReal _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hu, hfinite⟩

def source (u : Lp PhotonFock 2 μ) (hfinite : ∫⁻ x, radiationForm (u x) ∂μ < ⊤) :
    SpatialRadiationGraph μ := (graphValue_memLp u hfinite).toLp _

theorem source_inclusion (u : Lp PhotonFock 2 μ)
    (hfinite : ∫⁻ x, radiationForm (u x) ∂μ < ⊤) :
    spatialRadiationInclusion μ (source u hfinite) = u := by
  apply Lp.ext
  filter_upwards [radiationGraphInclusion.coeFn_compLpL (source u hfinite),
    (graphValue_memLp u hfinite).coeFn_toLp,
    ae_lt_top' (radiationForm_aemeasurable (Lp.aestronglyMeasurable u)) hfinite.ne]
    with x hx hrep hf
  exact hx.trans ((congrArg radiationGraphInclusion hrep).trans
    (graphValue_inclusion (u x) ((radiationRoot_domain_iff_finite (u x)).mpr hf)))

theorem source_graph (s : SpatialRadiationGraph μ) :
    ∀ᵐ x ∂μ, (spatialRadiationInclusion μ s x, spatialRadiationDerivative μ s x) ∈
      radiationRoot.graph := by
  filter_upwards [radiationGraphInclusion.coeFn_compLpL s,
    radiationGraphDerivative.coeFn_compLpL s] with x hi hd
  exact (congrArg (fun p : PhotonFock × PhotonFock => p ∈ radiationRoot.graph)
    (Prod.ext hi hd)).mpr (s x).property

end Spatial

variable {X : Type} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]
  (B : StandardNormalTraceBackground)

theorem fullRadiationForm_finite_iff (u : Lp PhotonFock 2 μ) :
    (fullForm B μ (NormalPhoton.radiationForm B.normal (B.realization PhotonFock).functional)).expectation
      ((B.realization (Lp PhotonFock 2 μ)).rank.rankOne u) < ⊤ ↔
        ∃ s : SpatialRadiationGraph μ, spatialRadiationInclusion μ s = u := by
  constructor
  · intro hf
    have h := (congrArg (fun t : ℝ≥0∞ => t < ⊤) (fullRadiationForm_rankOne B μ u)).mp hf
    exact ⟨source u h, source_inclusion u h⟩
  · rintro ⟨s, rfl⟩
    exact (fullRadiationForm_graph B μ _ _ (source_graph s)).trans_lt ENNReal.ofReal_lt_top

end GptLean.PhysicalSpatialRadiationDomain
