import GptLean.SymmetricLift.L2Mollification
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.Thickening

/-! Local Sobolev mollification for arbitrary finite coordinate sets.
This permits the physical coordinates `Fin N × Fin 3` directly, without
an extra reindexing or measure-transport premise. -/

noncomputable section

namespace GptLean.Repair

open MeasureTheory ContinuousLinearMap Filter Metric GptLean.SymmetricLift
open scoped Convolution Topology ContDiff ENNReal

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def finiteApproximationBump (I : Type*) [Fintype I] (n : ℕ) :
    ContDiffBump (0 : EuclideanSpace ℝ I) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 * (1 / ((n : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

theorem finiteApproximationBump_rOut_tendsto :
    Tendsto (fun n => (finiteApproximationBump I n).rOut) atTop (𝓝 0) := by
  simpa only [finiteApproximationBump, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

def finiteMollification (f : EuclideanSpace ℝ I → E) (n : ℕ) :
    EuclideanSpace ℝ I → E :=
  f ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip, volume]
    ((finiteApproximationBump I n).normed volume)

theorem finiteMollification_contDiff {f : EuclideanSpace ℝ I → E}
    (hf : LocallyIntegrable f volume) (n : ℕ) :
    ContDiff ℝ ∞ (finiteMollification f n) :=
  (finiteApproximationBump I n).hasCompactSupport_normed.contDiff_convolution_right _ hf
    (finiteApproximationBump I n).contDiff_normed

theorem finiteMollification_hasLineDerivAt
    {f g : EuclideanSpace ℝ I → E} (hf : LocallyIntegrable f volume)
    {v : EuclideanSpace ℝ I}
    (hweak : ∀ φ : EuclideanSpace ℝ I → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, φ x • g x) = -(∫ x, fderiv ℝ φ x v • f x))
    (n : ℕ) (x : EuclideanSpace ℝ I) :
    HasLineDerivAt ℝ (finiteMollification f n) (finiteMollification g n x) x v := by
  let κ := (finiteApproximationBump I n).normed volume
  have hκ : ContDiff ℝ ∞ κ := (finiteApproximationBump I n).contDiff_normed
  have hκs : HasCompactSupport κ := (finiteApproximationBump I n).hasCompactSupport_normed
  let φ : EuclideanSpace ℝ I → ℝ := fun y => κ (x - y)
  have hφ : ContDiff ℝ ∞ φ := hκ.comp (contDiff_const.sub contDiff_id)
  have hφs : HasCompactSupport φ := hκs.comp_homeomorph (Homeomorph.subLeft x)
  have hφd : ∀ y, fderiv ℝ φ y v = -(fderiv ℝ κ (x - y) v) := by
    intro y
    have h := ((hκ.differentiable (by simp)) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change HasFDerivAt φ _ y at h
    rw [h.fderiv]
    simp
  have hw := hweak φ hφ hφs
  simp_rw [hφd, neg_smul, integral_neg, neg_neg] at hw
  let L : E →L[ℝ] ℝ →L[ℝ] E := (lsmul ℝ ℝ).flip
  have hκ1 : ContDiff ℝ 1 κ := hκ.of_le (by simp)
  have hd := (hκs.hasFDerivAt_convolution_right L hf hκ1 x).hasLineDerivAt v
  rw [convolution_precompR_apply L hf (hκs.fderiv ℝ)
    (hκ1.continuous_fderiv one_ne_zero) x v] at hd
  have he : (f ⋆[L, volume] (fun y => fderiv ℝ κ y v)) x = finiteMollification g n x :=
    hw.symm
  rw [he] at hd
  exact hd

theorem finite_localMemLp_two_locallyIntegrable {f : EuclideanSpace ℝ I → E}
    (hf : ∀ K, IsCompact K → MemLp f 2 (volume.restrict K)) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact MemLp.integrable (by norm_num) (hf K hK)

theorem finiteMollification_memLp_two_restrict {f : EuclideanSpace ℝ I → E}
    (hf : LocallyIntegrable f volume) (n : ℕ)
    {K : Set (EuclideanSpace ℝ I)} (hK : IsCompact K) :
    MemLp (finiteMollification f n) 2 (volume.restrict K) := by
  have hc := (finiteMollification_contDiff hf n).continuous
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC x hx

private theorem finiteMollification_eq_truncated
    (f : EuclideanSpace ℝ I → E) (K : Set (EuclideanSpace ℝ I))
    (n : ℕ) (hn : (finiteApproximationBump I n).rOut ≤ 1)
    {x : EuclideanSpace ℝ I} (hx : x ∈ K) :
    finiteMollification f n x =
      finiteMollification ((cthickening 1 K).indicator f) n x := by
  classical
  unfold finiteMollification convolution
  apply integral_congr_ae
  apply ae_of_all
  intro y
  by_cases hy : y ∈ cthickening 1 K
  · simp only [Set.indicator_of_mem hy]
  · have hzero : (finiteApproximationBump I n).normed volume (x - y) = 0 := by
      by_contra hne
      have hsup : x - y ∈ Function.support ((finiteApproximationBump I n).normed volume) := hne
      rw [(finiteApproximationBump I n).support_normed_eq] at hsup
      have hnorm : ‖x - y‖ < (finiteApproximationBump I n).rOut := by
        simpa only [mem_ball, dist_zero_right] using hsup
      have hd : dist y x ≤ 1 := by
        rw [dist_eq_norm, norm_sub_rev]
        exact hnorm.le.trans hn
      exact hy (mem_cthickening_of_dist_le y x 1 K hx hd)
    simp only [hzero, flip_apply, lsmul_apply, zero_smul]

/-- Strong local L2 approximation by the explicit finite-coordinate
mollifiers, obtained from compact truncation and convolution continuity. -/
theorem finiteMollification_tendsto_eLpNorm_sub
    {f : EuclideanSpace ℝ I → E}
    (hf : ∀ K, IsCompact K → MemLp f 2 (volume.restrict K))
    {K : Set (EuclideanSpace ℝ I)} (hK : IsCompact K) :
    Tendsto (fun n => eLpNorm (finiteMollification f n - f) 2 (volume.restrict K))
      atTop (𝓝 0) := by
  classical
  let J := cthickening 1 K
  have hJ : IsCompact J := hK.cthickening
  let : IsFiniteMeasure (volume.restrict J) :=
    isFiniteMeasure_restrict.mpr hJ.measure_lt_top.ne
  have hf₁ : Integrable (J.indicator f) volume :=
    (integrable_indicator_iff hJ.measurableSet).2
      (MemLp.integrable (by norm_num) (hf J hJ))
  have hf₂ : MemLp (J.indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hJ.measurableSet).2 (hf J hJ)
  have hglobal := tendsto_eLpNorm_convolution_sub
    (fun n => (finiteApproximationBump I n).integrable_normed (μ := volume))
    (Eventually.of_forall fun n => (finiteApproximationBump I n).nonneg_normed)
    (Eventually.of_forall fun n => (finiteApproximationBump I n).integral_normed)
    (ContDiffBump.tendsto_support_normed_smallSets
      (finiteApproximationBump_rOut_tendsto (I := I))) hf₁ hf₂
  have hglobal' : Tendsto
      (fun n => eLpNorm (finiteMollification (J.indicator f) n - J.indicator f) 2 volume)
      atTop (𝓝 0) := by
    simpa only [finiteMollification, convolution_flip] using hglobal
  have hrestrict : Tendsto
      (fun n => eLpNorm (finiteMollification (J.indicator f) n - J.indicator f) 2
        (volume.restrict K)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglobal'
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)
  apply hrestrict.congr'
  filter_upwards [(finiteApproximationBump_rOut_tendsto (I := I)).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  change finiteMollification (J.indicator f) n x - J.indicator f x =
    finiteMollification f n x - f x
  rw [← finiteMollification_eq_truncated f K n hn hx,
    Set.indicator_of_mem (self_subset_cthickening K hx)]

end GptLean.Repair
