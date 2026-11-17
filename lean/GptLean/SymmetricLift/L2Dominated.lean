import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Strong L2 convergence from an integrable bound on squared norms.
This is used for the singular operator derivative in the tensor lift. -/

noncomputable section

namespace GptLean.SymmetricLift

open MeasureTheory Filter
open scoped ENNReal Topology

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E]

theorem memLp_two_of_sq_norm_le {f : X → E} {b : X → ℝ}
    (hf : AEStronglyMeasurable f μ) (hb : Integrable b μ)
    (hle : ∀ᵐ x ∂μ, ‖f x‖ ^ 2 ≤ b x) : MemLp f 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hf).2
  apply hb.mono' (hf.norm.pow 2)
  filter_upwards [hle] with x hx
  change |‖f x‖ ^ 2| ≤ b x
  rwa [abs_of_nonneg (sq_nonneg ‖f x‖)]

/-- Almost everywhere convergence with a common integrable square bound
implies convergence of the actual L2 seminorm of the difference. -/
theorem tendsto_eLpNorm_two_of_dominated_sq
    {f : ℕ → X → E} {g : X → E} {b : X → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : AEStronglyMeasurable g μ) (hb : Integrable b μ)
    (hfb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ^ 2 ≤ b x)
    (hgb : ∀ᵐ x ∂μ, ‖g x‖ ^ 2 ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0) := by
  have hdiff : ∀ n, ∀ᵐ x ∂μ, ‖f n x - g x‖ ^ 2 ≤ 4 * b x := by
    intro n
    filter_upwards [hfb n, hgb] with x hfx hgx
    have htri := norm_sub_le (f n x) (g x)
    have hnn := norm_nonneg (f n x - g x)
    have hfn := norm_nonneg (f n x)
    have hgn := norm_nonneg (g x)
    nlinarith [sq_nonneg (‖f n x‖ - ‖g x‖)]
  have hmem : ∀ n, MemLp (f n - g) 2 μ := fun n =>
    memLp_two_of_sq_norm_le ((hf n).sub hg) (hb.const_mul 4) (hdiff n)
  have hint : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => ‖f n x - g x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun x => 4 * b x) (fun n => ((hf n).sub hg).norm.pow 2)
      (hb.const_mul 4) (fun n => ?_) ?_
    · simpa using h
    · filter_upwards [hdiff n] with x hx
      change |‖f n x - g x‖ ^ 2| ≤ 4 * b x
      rwa [abs_of_nonneg (sq_nonneg ‖f n x - g x‖)]
    · filter_upwards [hlim] with x hx
      simpa using (hx.sub (tendsto_const_nhds (x := g x))).norm.pow 2
  have hp := ((Real.continuous_rpow_const (q := (2 : ℝ)⁻¹) (by positivity)).tendsto 0).comp hint
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp
  convert he using 1
  · funext n
    rw [(hmem n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp
  · norm_num

/-- The dominated convergence statement in the normed L2 space itself. -/
theorem tendsto_toLp_two_of_dominated_sq
    {f : ℕ → X → E} {g : X → E} {b : X → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hb : Integrable b μ)
    (hfb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ^ 2 ≤ b x)
    (hgb : ∀ᵐ x ∂μ, ‖g x‖ ^ 2 ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).2
  exact tendsto_eLpNorm_two_of_dominated_sq
    (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable hb hfb hgb hlim

end GptLean.SymmetricLift
