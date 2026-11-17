import GptLean.SymmetricLift.BoundedMollification
import GptLean.SymmetricLift.L2Mollification

/-!
The concrete ambient mollifiers converge strongly in L2 on every compact
set. The proof truncates the input on a compact neighborhood and applies
the global convolution theorem. No smooth approximation premise is assumed.
-/

noncomputable section
namespace GptLean.SymmetricLift

open MeasureTheory Filter Metric
open scoped ENNReal Topology Convolution

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Compact-local L2 membership implies local integrability. -/
theorem localMemLp_two_locallyIntegrable {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : ∀ K, IsCompact K → MemLp f 2 (volume.restrict K)) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact MemLp.integrable (by norm_num) (hf K hK)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Continuous functions belong to L2 on compact sets. -/
theorem continuous_memLp_two_restrict {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : Continuous f) {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) :
    MemLp f 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC x hx

omit [CompleteSpace E] in
/-- Every mollified field is locally L2, including the initial wide kernels. -/
theorem boundedMollification_memLp_two_restrict {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : LocallyIntegrable f volume) (n : ℕ)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) :
    MemLp (boundedMollification f n) 2 (volume.restrict K) :=
  continuous_memLp_two_restrict (boundedMollification_contDiff hf n).continuous hK

/-- Local L2 convergence of the actual mollifier sequence, obtained by
compact truncation and global strong continuity of convolution. -/
theorem boundedMollification_tendsto_eLpNorm_sub
    {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : ∀ K, IsCompact K → MemLp f 2 (volume.restrict K))
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) :
    Tendsto (fun n => eLpNorm (boundedMollification f n - f) 2 (volume.restrict K))
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
    (fun n => (approximationBump d n).integrable_normed (μ := volume))
    (Eventually.of_forall fun n => (approximationBump d n).nonneg_normed)
    (Eventually.of_forall fun n => (approximationBump d n).integral_normed)
    (ContDiffBump.tendsto_support_normed_smallSets (approximationBump_rOut_tendsto d))
    hf₁ hf₂
  have hglobal' : Tendsto
      (fun n => eLpNorm (boundedMollification (J.indicator f) n - J.indicator f) 2 volume)
      atTop (𝓝 0) := by
    simpa only [boundedMollification, smoothMollify, convolution_flip] using hglobal
  have hrestrict : Tendsto
      (fun n => eLpNorm (boundedMollification (J.indicator f) n - J.indicator f) 2
        (volume.restrict K)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglobal'
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)
  apply hrestrict.congr'
  filter_upwards [(approximationBump_rOut_tendsto d).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  change boundedMollification (J.indicator f) n x - J.indicator f x =
    boundedMollification f n x - f x
  rw [← boundedMollification_eq_truncated f K n hn hx,
    Set.indicator_of_mem (self_subset_cthickening K hx)]

end GptLean.SymmetricLift
