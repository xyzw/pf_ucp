import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic

/-!
Countable Bochner sums used in `lem-soft-disintegration`.
The finite integral of the sum of norms is an input. Pointwise convergence,
strong measurability of the sum, its integrability and interchange with the
integral are proved, including the common almost-everywhere set.
-/

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology

variable {Q T : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

omit [NormedSpace ℝ T] [CompleteSpace T] in
theorem ae_summable_norm_of_finite_total
    {F : ℕ → Q → T} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hfinite : ∑' n, ∫⁻ u, ‖F n u‖ₑ ∂μ ≠ ⊤) :
    ∀ᵐ u ∂μ, Summable (fun n => ‖F n u‖) := by
  have hm : ∀ n, AEMeasurable (fun u => ‖F n u‖ₑ) μ := fun n => (hF n).enorm
  have htotal : ∫⁻ u, ∑' n, ‖F n u‖ₑ ∂μ ≠ ⊤ := by
    rwa [lintegral_tsum hm]
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) htotal] with u hu
  exact tsum_enorm_ne_top_iff_summable_norm.mp hu.ne

omit [NormedSpace ℝ T] in
theorem ae_summable_of_finite_total
    {F : ℕ → Q → T} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hfinite : ∑' n, ∫⁻ u, ‖F n u‖ₑ ∂μ ≠ ⊤) :
    ∀ᵐ u ∂μ, Summable (fun n => F n u) := by
  filter_upwards [ae_summable_norm_of_finite_total hF hfinite] with u hu
  exact hu.of_norm

omit [NormedSpace ℝ T] in
theorem aestronglyMeasurable_series
    {F : ℕ → Q → T} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hfinite : ∑' n, ∫⁻ u, ‖F n u‖ₑ ∂μ ≠ ⊤) :
    AEStronglyMeasurable (fun u => ∑' n, F n u) μ := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun s : Finset ℕ => fun u => ∑ n ∈ s, F n u)
  · intro s
    exact s.aestronglyMeasurable_fun_sum (fun n _ => hF n)
  · filter_upwards [ae_summable_of_finite_total hF hfinite] with u hu
    exact hu.hasSum

theorem integrable_series
    {F : ℕ → Q → T} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hfinite : ∑' n, ∫⁻ u, ‖F n u‖ₑ ∂μ ≠ ⊤) :
    Integrable (fun u => ∑' n, F n u) μ := by
  refine ⟨aestronglyMeasurable_series hF hfinite, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    ∫⁻ u, ‖∑' n, F n u‖ₑ ∂μ ≤ ∫⁻ u, ∑' n, ‖F n u‖ₑ ∂μ :=
      lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = ∑' n, ∫⁻ u, ‖F n u‖ₑ ∂μ := lintegral_tsum (fun n => (hF n).enorm)
    _ < ⊤ := lt_top_iff_ne_top.mpr hfinite

omit [CompleteSpace T] in
theorem bochner_series_integral
    {F : ℕ → Q → T} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hfinite : ∑' n, ∫⁻ u, ‖F n u‖ₑ ∂μ ≠ ⊤) :
    ∫ u, ∑' n, F n u ∂μ = ∑' n, ∫ u, F n u ∂μ :=
  integral_tsum hF hfinite

theorem observable_series_ae
    {F : ℕ → Q → T} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hfinite : ∑' n, ∫⁻ u, ‖F n u‖ₑ ∂μ ≠ ⊤) (B : T →L[ℝ] ℝ) :
    ∀ᵐ u ∂μ, B (∑' n, F n u) = ∑' n, B (F n u) := by
  filter_upwards [ae_summable_of_finite_total hF hfinite] with u hu
  exact B.map_tsum hu

/-- The sum/integral exchange for a bounded measurable complex test and a
bounded observable. This is the analytic exchange in the disintegration proof. -/
theorem bounded_test_series_duality
    {F : ℕ → Q → T} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hfinite : ∑' n, ∫⁻ u, ‖F n u‖ₑ ∂μ ≠ ⊤)
    (B : T →L[ℝ] ℂ) {f : Q → ℂ} (hf : AEStronglyMeasurable f μ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ u ∂μ, ‖f u‖ ≤ M) :
    (∑' n, ∫ u, f u * B (F n u) ∂μ) =
      ∫ u, f u * B (∑' n, F n u) ∂μ := by
  have hnmeas : ∀ n, AEStronglyMeasurable (fun u => ‖F n u‖) μ := fun n => (hF n).norm
  have hnfinite : ∑' n, ∫⁻ u, ‖‖F n u‖‖ₑ ∂μ ≠ ⊤ := by
    simpa only [enorm_norm] using hfinite
  have hnormint := integrable_series hnmeas hnfinite
  apply HasSum.tsum_eq
  apply hasSum_integral_of_dominated_convergence
    (fun n u => (M * ‖B‖) * ‖F n u‖)
  · intro n
    exact hf.mul (B.continuous.comp_aestronglyMeasurable (hF n))
  · intro n
    filter_upwards [hbound] with u hu
    calc
      ‖f u * B (F n u)‖ = ‖f u‖ * ‖B (F n u)‖ := norm_mul _ _
      _ ≤ M * (‖B‖ * ‖F n u‖) :=
        mul_le_mul hu (B.le_opNorm _) (norm_nonneg _) hM
      _ = M * ‖B‖ * ‖F n u‖ := (mul_assoc _ _ _).symm
  · filter_upwards [ae_summable_norm_of_finite_total hF hfinite] with u hu
    exact hu.mul_left (M * ‖B‖)
  · simpa only [tsum_mul_left] using hnormint.const_mul (M * ‖B‖)
  · filter_upwards [ae_summable_of_finite_total hF hfinite] with u hu
    exact (B.hasSum hu.hasSum).mul_left (f u)

end GptLean.Gaussian
