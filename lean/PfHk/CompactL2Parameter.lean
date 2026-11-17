import PfHk.L2OperatorDerivative
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Strong L2 differentiation of a continuous family over a compact
parameter space. The local slope domination is proved from the continuous
fiber derivative, so callers supply no differentiability of Lp choices. -/

noncomputable section
namespace PfHk.CompactL2Parameter

open MeasureTheory Filter
open scoped ENNReal Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] {μ : Measure K} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem section_memLp {f : ℝ × K → E} (hf : Continuous f) (t : ℝ) :
    MemLp (fun k => f (t, k)) 2 μ :=
  (hf.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def sectionLp (f : ℝ × K → E) (hf : Continuous f) (t : ℝ) : Lp E 2 μ :=
  (section_memLp (μ := μ) hf t).toLp (fun k => f (t, k))

theorem sectionLp_continuous {f : ℝ × K → E} (hf : Continuous f) :
    Continuous (sectionLp (μ := μ) f hf) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro tn htn
  obtain ⟨B, hB⟩ := ((isCompact_Icc : IsCompact (Set.Icc (t - 1) (t + 1))).prod
    (isCompact_univ : IsCompact (Set.univ : Set K))).exists_bound_of_continuousOn hf.continuousOn
  let D := max B 0
  have hb (s : ℝ) (hs : s ∈ Set.Icc (t - 1) (t + 1)) (k : K) : ‖f (s, k)‖ ≤ D :=
    (hB (s, k) ⟨hs, Set.mem_univ k⟩).trans (le_max_left _ _)
  apply L2ParameterDerivative.tendsto_toLp_of_eventually_dominated_sq
    (fun n => section_memLp hf (tn n)) (section_memLp hf t) (integrable_const (D ^ 2))
  · have he := htn.eventually (Ioo_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))
    filter_upwards [he] with n hn
    exact ae_of_all _ fun k => pow_le_pow_left₀ (norm_nonneg _)
      (hb (tn n) ⟨hn.1.le, hn.2.le⟩ k) 2
  · exact ae_of_all _ fun k => pow_le_pow_left₀ (norm_nonneg _)
      (hb t ⟨by linarith, by linarith⟩ k) 2
  · exact ae_of_all _ fun k => hf.continuousAt.tendsto.comp (htn.prodMk_nhds tendsto_const_nhds)

theorem sectionLp_hasDerivAt {f df : ℝ × K → E} (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ k t, HasDerivAt (fun s => f (s, k)) (df (t, k)) t) (t : ℝ) :
    L2OperatorDerivative.HasL2DerivAt (sectionLp (μ := μ) f hf)
      (sectionLp (μ := μ) df hdf t) t := by
  obtain ⟨B, hB⟩ := ((isCompact_Icc : IsCompact (Set.Icc (t - 1) (t + 1))).prod
    (isCompact_univ : IsCompact (Set.univ : Set K))).exists_bound_of_continuousOn hdf.continuousOn
  let D := max B 0
  have hD : 0 ≤ D := le_max_right _ _
  have hb (s : ℝ) (hs : s ∈ Set.Icc (t - 1) (t + 1)) (k : K) : ‖df (s, k)‖ ≤ D :=
    (hB (s, k) ⟨hs, Set.mem_univ k⟩).trans (le_max_left _ _)
  apply L2ParameterDerivative.hasDerivAt_toLp
    (fun s => section_memLp hf s) (section_memLp hdf t) (integrable_const (D ^ 2))
  · exact ae_of_all _ fun k => hd k t
  · have hh : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hh] with h hh
    apply ae_of_all
    intro k
    exact pow_le_pow_left₀ (norm_nonneg _)
      (L2ParameterDerivative.local_slope_norm_le hD (fun s _ => hd k s)
        (fun s hs => hb s hs k) (abs_le.mpr ⟨hh.1.le, hh.2.le⟩)) 2
  · exact ae_of_all _ fun k => pow_le_pow_left₀ (norm_nonneg _)
      (hb t ⟨by linarith, by linarith⟩ k) 2

end PfHk.CompactL2Parameter
