/-
Adapted from the repository's claude_lean/QEDFT/Attainment/CutoffProfile.lean.
The mathematical proof bodies are retained and rechecked independently under
GptLean. No QEDFT modules are imported.
-/
import GptLean.LayerCake
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Actual cutoff moments for `infrared-kernel-errors` and `cutoff-assumption`.

`bsq κ` and `asq κ` are the real values of the nonnegative Lebesgue integrals
of `w` and `w / ω` over `ω < κ`. Measurable dispersion, positivity almost
everywhere, and finite total weighted integrals are explicit hypotheses.
For `w = |χ̂|²` these are exactly the cutoff assumptions needed here.

The file proves monotonicity, nonnegativity and decay of these moments and
their square roots as `κ ↓ 0`. It also proves the integrability and the real
Tonelli estimate for `bsq t / t²` used before
`unrestricted-near-minimizer-number`. No cutoff convergence or integrability
is left as an axiom or model-specific hypothesis in these results.

Identifying these abstract integrals with the norms of the article's field
kernels is outside this module. The generality includes the massless
three-dimensional momentum dispersion once its standard measurable and
almost everywhere positive properties have been supplied.
-/

namespace GptLean.CutoffProfile

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ω : Ω → ℝ) (w : Ω → ℝ≥0∞)

noncomputable def bsq (κ : ℝ) : ℝ := (∫⁻ x in {x | ω x < κ}, w x ∂μ).toReal

noncomputable def asq (κ : ℝ) : ℝ := (∫⁻ x in {x | ω x < κ}, w x * ENNReal.ofReal (1 / ω x) ∂μ).toReal

variable {μ ω w}

theorem bsq_nonneg (κ : ℝ) : 0 ≤ bsq μ ω w κ := ENNReal.toReal_nonneg

theorem asq_nonneg (κ : ℝ) : 0 ≤ asq μ ω w κ := ENNReal.toReal_nonneg

omit [MeasurableSpace Ω] in

theorem sublevel_mono {κ κ' : ℝ} (h : κ ≤ κ') : {x | ω x < κ} ⊆ {x | ω x < κ'} :=
  fun _ hx => lt_of_lt_of_le hx h

theorem bsq_mono (hB : ∫⁻ x, w x ∂μ < ⊤) : Monotone (bsq μ ω w) := fun _ _ h =>
  ENNReal.toReal_mono (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hB).ne
    (lintegral_mono_set (sublevel_mono h))

theorem asq_mono (hA : ∫⁻ x, w x * ENNReal.ofReal (1 / ω x) ∂μ < ⊤) :
    Monotone (asq μ ω w) := fun _ _ h =>
  ENNReal.toReal_mono (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hA).ne
    (lintegral_mono_set (sublevel_mono h))

section Tendsto

variable (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)

theorem measure_nonpos_eq_zero (hpos : ∀ᵐ x ∂μ, 0 < ω x) : μ {x | ω x ≤ 0} = 0 := by
  rw [ae_iff] at hpos
  simpa only [not_lt] using hpos

theorem tendsto_setLIntegral_sublevel (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)
    {f : Ω → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ < ⊤) :
    Tendsto (fun κ => ∫⁻ x in {x | ω x < κ}, f x ∂μ) (𝓝[>] 0) (𝓝 0) := by
  set ν := μ.withDensity f with hν
  have hmeas : ∀ κ : ℝ, MeasurableSet {x | ω x < κ} := fun κ => hω measurableSet_Iio
  have heq : ∀ κ, ∫⁻ x in {x | ω x < κ}, f x ∂μ = ν {x | ω x < κ} := fun κ =>
    (withDensity_apply f (hmeas κ)).symm
  simp_rw [heq]
  have hlim := tendsto_measure_biInter_gt (μ := ν) (a := (0 : ℝ)) (s := fun κ => {x | ω x < κ})
    (fun r _ => (hmeas r).nullMeasurableSet) (fun i j _ hij => sublevel_mono hij)
    ⟨1, one_pos, by
      rw [withDensity_apply f (hmeas 1)]
      exact (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hf).ne⟩
  have hinter : (⋂ r > (0 : ℝ), {x | ω x < r}) = {x | ω x ≤ 0} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h
      by_contra hx
      have hx' : 0 < ω x := lt_of_not_ge hx
      exact lt_irrefl _ (h (ω x) hx')
    · intro h r hr
      exact lt_of_le_of_lt h hr
  rw [hinter] at hlim
  have hnull : ν {x | ω x ≤ 0} = 0 :=
    withDensity_absolutelyContinuous μ f (measure_nonpos_eq_zero hpos)
  rw [hnull] at hlim
  exact hlim

theorem tendsto_bsq (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)
    (hB : ∫⁻ x, w x ∂μ < ⊤) : Tendsto (bsq μ ω w) (𝓝[>] 0) (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_setLIntegral_sublevel hω hpos hB)
  rw [ENNReal.toReal_zero] at h
  exact h

theorem tendsto_asq (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)
    (hA : ∫⁻ x, w x * ENNReal.ofReal (1 / ω x) ∂μ < ⊤) :
    Tendsto (asq μ ω w) (𝓝[>] 0) (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_setLIntegral_sublevel hω hpos hA)
  rw [ENNReal.toReal_zero] at h
  exact h

theorem tendsto_sqrt_bsq (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)
    (hB : ∫⁻ x, w x ∂μ < ⊤) : Tendsto (fun κ => √(bsq μ ω w κ)) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp (tendsto_bsq hω hpos hB)
  simpa [Function.comp_def] using h

theorem tendsto_sqrt_asq (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)
    (hA : ∫⁻ x, w x * ENNReal.ofReal (1 / ω x) ∂μ < ⊤) :
    Tendsto (fun κ => √(asq μ ω w κ)) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp (tendsto_asq hω hpos hA)
  simpa [Function.comp_def] using h

/-- Actual cutoff decay supplies both smallness conditions used by
`Attainment.raw_fixed_scale_soft_energy_gain`. The fixed choice `R = κ⁻¹`
therefore needs no additional cutoff hypothesis beyond weighted finiteness. -/
theorem eventually_fixed_scale_small (hω : Measurable ω)
    (hpos : ∀ᵐ x ∂μ, 0 < ω x)
    (hA : ∫⁻ x, w x * ENNReal.ofReal (1 / ω x) ∂μ < ⊤) (C e : ℝ) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ),
      C * e ^ 2 * (Real.sqrt (asq μ ω w κ)) ^ 2 ≤ 1 / 4 ∧
        (Real.sqrt (asq μ ω w κ)) ^ 2 ≤ 1 := by
  have hlim := tendsto_asq hω hpos hA
  have hscaled : Tendsto (fun κ => C * e ^ 2 * asq μ ω w κ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hlim.const_mul (C * e ^ 2)
  filter_upwards [hscaled.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with κ hsmall hbound
  rw [Real.sq_sqrt (asq_nonneg κ)]
  exact ⟨hsmall.le, hbound.le⟩

end Tendsto

section Tonelli

variable (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x) (hw : Measurable w)
  (hB : ∫⁻ x, w x ∂μ < ⊤) (hA : ∫⁻ x, w x * ENNReal.ofReal (1 / ω x) ∂μ < ⊤)

include hB in

theorem ofReal_bsq_div_sq (t : ℝ) :
    (∫⁻ x in {x | ω x < t}, w x ∂μ) * ENNReal.ofReal (1 / t ^ 2)
      = ENNReal.ofReal (bsq μ ω w t / t ^ 2) := by
  have hfin : ∫⁻ x in {x | ω x < t}, w x ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hB).ne
  rw [div_eq_mul_one_div (bsq μ ω w t), ENNReal.ofReal_mul (bsq_nonneg t), bsq,
    ENNReal.ofReal_toReal hfin]

include hB in

theorem measurable_bsq_div_sq : Measurable fun t : ℝ => bsq μ ω w t / t ^ 2 :=
  (bsq_mono hB).measurable.div (measurable_id.pow_const 2)

include hω hpos hw hB hA in
variable [SFinite μ] in

theorem lintegral_bsq_div_sq_le {κ₀ : ℝ} (hκ₀ : 0 < κ₀) :
    ∫⁻ t in Ioc 0 κ₀, ENNReal.ofReal (bsq μ ω w t / t ^ 2) ≤ ENNReal.ofReal (asq μ ω w κ₀) := by
  have h1 : ∫⁻ t in Ioc 0 κ₀, ENNReal.ofReal (bsq μ ω w t / t ^ 2)
      = ∫⁻ t in Ioc 0 κ₀, (∫⁻ x in {x | ω x < t}, w x ∂μ) * ENNReal.ofReal (1 / t ^ 2) := by
    refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    exact (ofReal_bsq_div_sq hB t).symm
  have hfin : ∫⁻ x in {x | ω x < κ₀}, w x * ENNReal.ofReal (1 / ω x) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hA).ne
  rw [h1, asq, ENNReal.ofReal_toReal hfin]
  exact GptLean.LayerCake.tonelli_infrared_le μ hω hpos hw hκ₀

include hω hpos hw hB hA in
variable [SFinite μ] in

theorem integrableOn_bsq_div_sq {κ₀ : ℝ} (hκ₀ : 0 < κ₀) :
    IntegrableOn (fun t => bsq μ ω w t / t ^ 2) (Ioc 0 κ₀) := by
  refine ⟨(measurable_bsq_div_sq hB).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun t => by
    exact div_nonneg (bsq_nonneg t) (sq_nonneg t))]
  exact lt_of_le_of_lt (lintegral_bsq_div_sq_le hω hpos hw hB hA hκ₀) ENNReal.ofReal_lt_top

include hω hpos hw hB hA in
variable [SFinite μ] in

theorem integral_bsq_div_sq_le {κ₀ : ℝ} (hκ₀ : 0 < κ₀) :
    ∫ t in (0 : ℝ)..κ₀, bsq μ ω w t / t ^ 2 ≤ asq μ ω w κ₀ := by
  rw [intervalIntegral.integral_of_le hκ₀.le,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t => div_nonneg (bsq_nonneg t) (sq_nonneg t))
      (measurable_bsq_div_sq hB).aestronglyMeasurable]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_bsq_div_sq_le hω hpos hw hB hA hκ₀)).trans ?_
  rw [ENNReal.toReal_ofReal (asq_nonneg κ₀)]

end Tonelli

end GptLean.CutoffProfile
