import PfHk.L2ParameterDerivative

/-! Strong continuity in L2 follows from pointwise continuity and a local
square-integrable dominator. This applies to the physical parameter
coefficients without differentiating those coefficients again. -/

noncomputable section
namespace PfHk.L2ParameterContinuity

open MeasureTheory Filter
open scoped ENNReal Topology

set_option maxHeartbeats 20000
set_option Elab.async false

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] {μ : Measure X}

theorem continuousAt_of_representatives {f : ℝ → Lp H 2 μ} {φ : ℝ → X → H}
    {t : ℝ} {b : X → ℝ}
    (hrep : ∀ s, f s =ᵐ[μ] φ s)
    (hc : ∀ᵐ x ∂μ, ContinuousAt (fun s => φ s x) t)
    (hb : Integrable b μ)
    (hbound : ∀ᶠ s in 𝓝 t, ∀ᵐ x ∂μ, ‖φ s x‖ ^ 2 ≤ b x) :
    ContinuousAt f t := by
  have hmem (s : ℝ) : MemLp (φ s) 2 μ := (Lp.memLp (f s)).ae_eq (hrep s)
  have heq (s : ℝ) : (hmem s).toLp (φ s) = f s :=
    Lp.ext ((hmem s).coeFn_toLp.trans (hrep s).symm)
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro sn hsn
  have h := L2ParameterDerivative.tendsto_toLp_of_eventually_dominated_sq
    (fun n => hmem (sn n)) (hmem t) hb (hsn.eventually hbound)
    hbound.self_of_nhds (hc.mono fun x hx => hx.tendsto.comp hsn)
  simpa only [heq, Function.comp_def] using h

theorem continuousAt_of_norm_bound {Q : Type*} [NormedAddCommGroup Q]
    {f : ℝ → Lp H 2 μ} {φ : ℝ → X → H} (q : Lp Q 2 μ) {t C : ℝ}
    (hrep : ∀ s, f s =ᵐ[μ] φ s)
    (hc : ∀ᵐ x ∂μ, ContinuousAt (fun s => φ s x) t)
    (hbound : ∀ᶠ s in 𝓝 t, ∀ᵐ x ∂μ, ‖φ s x‖ ≤ C * ‖q x‖) :
    ContinuousAt f t := by
  apply continuousAt_of_representatives hrep hc
    ((Lp.memLp q).norm.integrable_sq.const_mul (C^2))
  filter_upwards [hbound] with s hs
  filter_upwards [hs] with x hx
  exact (pow_le_pow_left₀ (norm_nonneg _) hx 2).trans_eq (mul_pow C ‖q x‖ 2)

end PfHk.L2ParameterContinuity
