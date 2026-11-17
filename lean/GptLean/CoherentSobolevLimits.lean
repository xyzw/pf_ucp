import GptLean.RepresentabilityCoherentSobolev
import Mathlib.MeasureTheory.Function.Holder

/-! Strong L1 and L2 passages for the complex coherent-state chain rule. -/

noncomputable section

namespace GptLean.Representability

open MeasureTheory Filter SymmetricLift
open scoped ENNReal Topology

set_option Elab.async false
set_option maxHeartbeats 800000

section Limits

variable {X P Q E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous bilinear maps take strong L2 convergence to strong L1 convergence. -/
theorem bilinear_tendsto_eLpNorm_one (B : P →L[ℝ] Q →L[ℝ] E)
    {f : ℕ → X → P} {f₀ : X → P} {g : ℕ → X → Q} {g₀ : X → Q}
    (hf : ∀ n, MemLp (f n) 2 μ) (hf₀ : MemLp f₀ 2 μ)
    (hg : ∀ n, MemLp (g n) 2 μ) (hg₀ : MemLp g₀ 2 μ)
    (hflim : Tendsto (fun n => eLpNorm (f n - f₀) 2 μ) atTop (𝓝 0))
    (hglim : Tendsto (fun n => eLpNorm (g n - g₀) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      ((fun x => B (f n x) (g n x)) - fun x => B (f₀ x) (g₀ x)) 1 μ) atTop (𝓝 0) := by
  have hlf := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf f₀ hf₀).mpr hflim
  have hlg := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg g₀ hg₀).mpr hglim
  have hc : Continuous (fun p : Lp P 2 μ × Lp Q 2 μ => (B.holderL μ 2 2 1) p.1 p.2) :=
    ((B.holderL μ 2 2 1).continuous.comp continuous_fst).clm_apply continuous_snd
  have he (u : X → P) (v : X → Q) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
      (B.holderL μ 2 2 1) (hu.toLp u) (hv.toLp v) =
        (B.memLp_of_bilin 1 hu hv).toLp (fun x => B (u x) (v x)) := by
    apply Lp.ext
    filter_upwards [B.coeFn_holder (r := 1) (hu.toLp u) (hv.toLp v), hu.coeFn_toLp, hv.coeFn_toLp,
      (B.memLp_of_bilin 1 hu hv).coeFn_toLp] with x h₁ h₂ h₃ h₄
    exact h₁.trans ((congrArg₂ (fun a b => B a b) h₂ h₃).trans h₄.symm)
  have h := (hc.tendsto (hf₀.toLp f₀, hg₀.toLp g₀)).comp (hlf.prodMk_nhds hlg)
  rw [he f₀ g₀ hf₀ hg₀] at h
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => B.memLp_of_bilin 1 (hf n) (hg n))
    _ (B.memLp_of_bilin 1 hf₀ hg₀)).mp
      (h.congr' (Eventually.of_forall fun n => he (f n) (g n) (hf n) (hg n)))

omit [NormedSpace ℝ E] in
/-- Domination by an integrable norm gives strong L1 convergence. -/
theorem tendsto_eLpNorm_one_of_dominated
    {f : ℕ → X → E} {g : X → E} {b : X → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hb : Integrable b μ) (hfb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ b x)
    (hgb : ∀ᵐ x ∂μ, ‖g x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) := by
  have hdiff (n) : ∀ᵐ x ∂μ, ‖f n x - g x‖ ≤ 2 * b x := by
    filter_upwards [hfb n, hgb] with x hf hg
    exact (norm_sub_le _ _).trans (by linarith)
  have hm (n) : MemLp (f n - g) 1 μ :=
    memLp_one_iff_integrable.mpr ((hb.const_mul 2).mono' ((hf n).sub hg) (hdiff n))
  have ht : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => ‖f n x - g x‖) (f := fun _ => (0 : ℝ)) (fun x => 2 * b x)
      (fun n => ((hf n).sub hg).norm) (hb.const_mul 2)
      (fun n => (hdiff n).mono fun x hx => by simpa only [norm_norm] using hx) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [hlim] with x hx
      simpa only [sub_self, norm_zero] using (hx.sub (tendsto_const_nhds (x := g x))).norm
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  convert h using 1
  · funext n
    rw [(hm n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp
  · simp

/-- A bounded vector factor may vary pointwise while its scalar coefficient
converges strongly in L1. -/
theorem bounded_smul_tendsto_eLpNorm_one
    {a : ℕ → X → ℝ} {a₀ : X → ℝ} {v : ℕ → X → E} {v₀ : X → E}
    (ha : ∀ n, Integrable (a n) μ) (ha₀ : Integrable a₀ μ)
    (hv : ∀ n, AEStronglyMeasurable (v n) μ) (hv₀ : AEStronglyMeasurable v₀ μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n x, ‖v n x‖ ≤ C) (hb₀ : ∀ x, ‖v₀ x‖ ≤ C)
    (halim : Tendsto (fun n => eLpNorm (a n - a₀) 1 μ) atTop (𝓝 0))
    (hvlim : ∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 (v₀ x))) :
    Tendsto (fun n => eLpNorm
      ((fun x => a n x • v n x) - fun x => a₀ x • v₀ x) 1 μ) atTop (𝓝 0) := by
  let u n := fun x => (a n x - a₀ x) • v n x
  let w n := (fun x => a₀ x • v n x) - fun x => a₀ x • v₀ x
  have hum (n) : AEStronglyMeasurable (u n) μ :=
    ((ha n).aestronglyMeasurable.sub ha₀.aestronglyMeasurable).smul (hv n)
  have hwm (n) : AEStronglyMeasurable (w n) μ :=
    (ha₀.aestronglyMeasurable.smul (hv n)).sub (ha₀.aestronglyMeasurable.smul hv₀)
  have hulim : Tendsto (fun n => eLpNorm (u n) 1 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) halim (Or.inr ENNReal.ofReal_ne_top))
      (fun _ => zero_le)
    intro n
    change eLpNorm (u n) 1 μ ≤ ENNReal.ofReal C * eLpNorm (a n - a₀) 1 μ
    exact (eLpNorm_mono_ae (ae_of_all _ fun x => by
      change ‖(a n x - a₀ x) • v n x‖ ≤ ‖C * (a n x - a₀ x)‖
      rw [norm_smul, norm_mul, Real.norm_of_nonneg hC, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hb n x) (norm_nonneg _))).trans_eq
        (by
          change eLpNorm (C • (a n - a₀)) 1 μ = ENNReal.ofReal C * eLpNorm (a n - a₀) 1 μ
          rw [eLpNorm_const_smul, Real.enorm_of_nonneg hC])
  have hwlim : Tendsto (fun n => eLpNorm (w n) 1 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_one_of_dominated
      (fun n => ha₀.aestronglyMeasurable.smul (hv n))
      (ha₀.aestronglyMeasurable.smul hv₀) (ha₀.norm.mul_const C)
    · intro n
      exact ae_of_all _ fun x => by
        change ‖a₀ x • v n x‖ ≤ ‖a₀ x‖ * C
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hb n x) (norm_nonneg _)
    · exact ae_of_all _ fun x => by
        change ‖a₀ x • v₀ x‖ ≤ ‖a₀ x‖ * C
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hb₀ x) (norm_nonneg _)
    · filter_upwards [hvlim] with x hx
      exact tendsto_const_nhds.smul hx
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using hulim.add hwlim) (fun _ => zero_le)
  intro n
  have he : ((fun x => a n x • v n x) - fun x => a₀ x • v₀ x) = u n + w n := by
    funext x
    simp only [u, w, Pi.sub_apply, Pi.add_apply, sub_smul]
    abel
  change eLpNorm ((fun x => a n x • v n x) - fun x => a₀ x • v₀ x) 1 μ ≤
    eLpNorm (u n) 1 μ + eLpNorm (w n) 1 μ
  rw [he]
  exact eLpNorm_add_le (hum n) (hwm n) (by norm_num)

/-- Strongly varying isometries act continuously on strongly convergent L2
fields. Only the actual vector fields need to be measurable. -/
theorem isometry_apply_tendsto_eLpNorm_two
    (U : ℕ → X → P →ₗᵢ[ℝ] E) (U₀ : X → P →ₗᵢ[ℝ] E)
    {f : ℕ → X → P} {f₀ : X → P}
    (hf₀ : MemLp f₀ 2 μ)
    (hmoving : ∀ n, AEStronglyMeasurable (fun x => U n x (f n x)) μ)
    (hfixed : ∀ n, AEStronglyMeasurable (fun x => U n x (f₀ x)) μ)
    (hzero : AEStronglyMeasurable (fun x => U₀ x (f₀ x)) μ)
    (hlim : Tendsto (fun n => eLpNorm (f n - f₀) 2 μ) atTop (𝓝 0))
    (hU : ∀ᵐ x ∂μ, Tendsto (fun n => U n x (f₀ x)) atTop (𝓝 (U₀ x (f₀ x)))) :
    Tendsto (fun n => eLpNorm
      ((fun x => U n x (f n x)) - fun x => U₀ x (f₀ x)) 2 μ) atTop (𝓝 0) := by
  let a n := (fun x => U n x (f n x)) - fun x => U n x (f₀ x)
  let b n := (fun x => U n x (f₀ x)) - fun x => U₀ x (f₀ x)
  have ha : Tendsto (fun n => eLpNorm (a n) 2 μ) atTop (𝓝 0) := by
    have he (n) : eLpNorm (a n) 2 μ = eLpNorm (f n - f₀) 2 μ := by
      apply eLpNorm_congr_norm_ae
      exact ae_of_all _ fun x => by
        change ‖U n x (f n x) - U n x (f₀ x)‖ = ‖f n x - f₀ x‖
        rw [← map_sub, (U n x).norm_map]
    simpa only [he] using hlim
  have hb : Tendsto (fun n => eLpNorm (b n) 2 μ) atTop (𝓝 0) := by
    exact tendsto_eLpNorm_two_of_dominated_sq hfixed hzero
      (hf₀.integrable_norm_pow (by norm_num))
      (fun n => ae_of_all _ fun x => by rw [(U n x).norm_map])
      (ae_of_all _ fun x => by rw [(U₀ x).norm_map]) hU
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using ha.add hb) (fun _ => zero_le)
  intro n
  have he : ((fun x => U n x (f n x)) - fun x => U₀ x (f₀ x)) = a n + b n := by
    funext x
    simp only [a, b, Pi.sub_apply, Pi.add_apply]
    abel
  change eLpNorm ((fun x => U n x (f n x)) - fun x => U₀ x (f₀ x)) 2 μ ≤
    eLpNorm (a n) 2 μ + eLpNorm (b n) 2 μ
  rw [he]
  exact eLpNorm_add_le ((hmoving n).sub (hfixed n)) ((hfixed n).sub hzero) (by norm_num)

omit [NormedSpace ℝ E] in
theorem tendsto_eLpNorm_add_one
    {f g : ℕ → X → E} {f₀ g₀ : X → E}
    (hf : ∀ n, MemLp (f n) 1 μ) (hg : ∀ n, MemLp (g n) 1 μ)
    (hf₀ : MemLp f₀ 1 μ) (hg₀ : MemLp g₀ 1 μ)
    (hflim : Tendsto (fun n => eLpNorm (f n - f₀) 1 μ) atTop (𝓝 0))
    (hglim : Tendsto (fun n => eLpNorm (g n - g₀) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((f n + g n) - (f₀ + g₀)) 1 μ) atTop (𝓝 0) := by
  have hF := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf f₀ hf₀).mpr hflim
  have hG := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg g₀ hg₀).mpr hglim
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => f n + g n)
    (fun n => (hf n).add (hg n)) (f₀ + g₀) (hf₀.add hg₀)).mp
  have hsum : (fun n => ((hf n).add (hg n)).toLp (f n + g n)) =
      (fun n => (hf n).toLp (f n) + (hg n).toLp (g n)) := by
    funext n
    exact MemLp.toLp_add (hf n) (hg n)
  rw [hsum, MemLp.toLp_add hf₀ hg₀]
  exact hF.add hG

end Limits

end GptLean.Representability
