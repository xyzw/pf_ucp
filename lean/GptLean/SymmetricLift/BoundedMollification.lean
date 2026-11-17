import GptLean.SymmetricLift.WeakMollification
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-! An explicit sequence of smooth ambient approximants preserving the
closed unit ball and converging almost everywhere. Its derivatives are
the mollifications of the weak derivatives. Strong local L2 convergence
of those derivatives is a separate statement. -/

noncomputable section

namespace GptLean.SymmetricLift

open MeasureTheory ContinuousLinearMap Filter Metric
open scoped Convolution Topology ContDiff

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def approximationBump (d n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 * (1 / ((n : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

theorem approximationBump_rOut_tendsto (d : ℕ) :
    Tendsto (fun n => (approximationBump d n).rOut) atTop (𝓝 0) := by
  simpa only [approximationBump, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

def boundedMollification (f : EuclideanSpace ℝ (Fin d) → E) (n : ℕ) :
    EuclideanSpace ℝ (Fin d) → E :=
  smoothMollify ((approximationBump d n).normed volume) f

omit [CompleteSpace E] in
theorem boundedMollification_contDiff {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : LocallyIntegrable f volume) (n : ℕ) :
    ContDiff ℝ ∞ (boundedMollification f n) :=
  smoothMollify_contDiff (approximationBump d n).contDiff_normed
    (approximationBump d n).hasCompactSupport_normed hf

theorem boundedMollification_norm_le_one {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : AEStronglyMeasurable f volume) (hbound : ∀ x, ‖f x‖ ≤ 1)
    (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ‖boundedMollification f n x‖ ≤ 1 := by
  have h := dist_convolution_le (μ := volume) (g := f) (x₀ := x) (z₀ := (0 : E))
    (by norm_num : (0 : ℝ) ≤ 1) (approximationBump d n).support_normed_eq.subset
    (approximationBump d n).nonneg_normed (approximationBump d n).integral_normed
    hf (fun y _ => by simpa using hbound y)
  simpa only [boundedMollification, smoothMollify, convolution_flip, dist_zero_right] using h

theorem boundedMollification_ae_tendsto {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume, Tendsto (fun n => boundedMollification f n x) atTop (𝓝 (f x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (approximationBump_rOut_tendsto d)
    (Filter.Eventually.of_forall (fun n =>
      (show (approximationBump d n).rOut ≤ 2 * (approximationBump d n).rIn from le_rfl))) hf
  simpa only [boundedMollification, smoothMollify, convolution_flip] using h

omit [CompleteSpace E] in
theorem boundedMollification_hasLineDerivAt
    {f g : EuclideanSpace ℝ (Fin d) → E} (hf : LocallyIntegrable f volume)
    {v : EuclideanSpace ℝ (Fin d)} (hweak : WeakDirectionalIdentity f g v)
    (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    HasLineDerivAt ℝ (boundedMollification f n) (boundedMollification g n x) x v :=
  smoothMollify_hasLineDerivAt (approximationBump d n).contDiff_normed
    (approximationBump d n).hasCompactSupport_normed hf hweak x

omit [CompleteSpace E] in
/-- On a fixed set, a sufficiently narrow mollifier only sees the function
on its closed unit neighborhood. This permits local L2 approximation to
be reduced to a compactly truncated global L1 and L2 function. -/
theorem boundedMollification_eq_truncated
    (f : EuclideanSpace ℝ (Fin d) → E) (K : Set (EuclideanSpace ℝ (Fin d)))
    (n : ℕ) (hn : (approximationBump d n).rOut ≤ 1)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ K) :
    boundedMollification f n x =
      boundedMollification ((cthickening 1 K).indicator f) n x := by
  classical
  simp only [boundedMollification, smoothMollify_apply]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  by_cases hy : y ∈ cthickening 1 K
  · simp only [Set.indicator_of_mem hy]
  · have hzero : (approximationBump d n).normed volume (x - y) = 0 := by
      by_contra hne
      have hsup : x - y ∈ Function.support ((approximationBump d n).normed volume) := hne
      rw [(approximationBump d n).support_normed_eq] at hsup
      have hnorm : ‖x - y‖ < (approximationBump d n).rOut := by
        simpa only [mem_ball, dist_zero_right] using hsup
      have hd : dist y x ≤ 1 := by
        rw [dist_eq_norm, norm_sub_rev]
        exact hnorm.le.trans hn
      exact hy (mem_cthickening_of_dist_le y x 1 K hx hd)
    simp only [hzero, zero_smul]

end GptLean.SymmetricLift
