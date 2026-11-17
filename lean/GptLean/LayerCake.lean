/-
Adapted from the repository's claude_lean/QEDFT/SoftPhoton/LayerCake.lean.
The mathematical proof bodies are retained and rechecked independently under
GptLean. No QEDFT modules are imported.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
Lebesgue integrals for the current `thm-unrestricted-attainment` proof.

The kernel is the indicator of `ω < t` multiplied by `t⁻²`. Its interval
integrals are evaluated exactly. Tonelli is applied on an arbitrary s-finite
measure space with measurable, almost everywhere positive dispersion `ω`.

For the cutoff profile `B(t) = ∫_{ω<t} |χ̂|²`, `tonelli_infrared_eq` and
`tonelli_infrared_le` establish the infrared identity and estimate before
`unrestricted-near-minimizer-number`. The quantities correspond to
`infrared-kernel-errors` in the current manuscript.

`integral_soft_profile_le` integrates `unrestricted-uniform-soft-energy`.
`number_bound_assembly` gives `unrestricted-near-minimizer-number` with explicit
constants. At zero excess, `photon_number_le` and `uniform_number_bound` are
applicable to `unrestricted-uniform-number` and `optimizer-soft-number-bound`.

These are theorems about genuine Lebesgue and interval integrals. The passage
from photon operators to such moments and the paper's soft-removal estimate
remain separate inputs. All needed measurability, positivity and integrability
conditions appear in the theorem statements.
-/

namespace GptLean
namespace LayerCake

open MeasureTheory Set

noncomputable def softKernel (ω t : ℝ) : ℝ := (Ioi ω).indicator (fun s : ℝ => 1 / s ^ 2) t

theorem softKernel_of_lt {ω t : ℝ} (h : ω < t) : softKernel ω t = 1 / t ^ 2 := by
  simp [softKernel, h]

theorem softKernel_of_le {ω t : ℝ} (h : t ≤ ω) : softKernel ω t = 0 := by
  simp [softKernel, h]

theorem softKernel_nonneg (ω t : ℝ) : 0 ≤ softKernel ω t := by
  unfold softKernel
  exact indicator_nonneg (fun s _ => by positivity) t

theorem integral_one_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / t ^ 2 = 1 / a - 1 / b := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    exact absurd h.1 (not_le.mpr ha)
  have e : ∀ t : ℝ, 1 / t ^ 2 = t ^ (-2 : ℤ) := fun t => by
    rw [zpow_neg, zpow_ofNat, one_div]
  have hb : 0 < b := ha.trans_le hab
  simp_rw [e]
  rw [integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num
  field_simp
  ring

theorem integral_softKernel {ω c κ₀ : ℝ} (hcκ : c ≤ κ₀) (hm : 0 < max ω c) :
    ∫ t in c..κ₀, softKernel ω t = if max ω c < κ₀ then 1 / max ω c - 1 / κ₀ else 0 := by
  have hset : Ioc c κ₀ ∩ Ioi ω = Ioc (max ω c) κ₀ := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi, max_lt_iff]
    tauto
  unfold softKernel
  rw [intervalIntegral.integral_of_le hcκ, setIntegral_indicator measurableSet_Ioi, hset]
  split_ifs with h
  · rw [← intervalIntegral.integral_of_le h.le, integral_one_div_sq hm h.le]
  · rw [Ioc_eq_empty h, Measure.restrict_empty, integral_zero_measure]

theorem integral_softKernel_zero {ω κ : ℝ} (hω : 0 < ω) (hκ : 0 < κ) :
    ∫ t in (0 : ℝ)..κ, softKernel ω t = if ω < κ then 1 / ω - 1 / κ else 0 := by
  have h := integral_softKernel (ω := ω) hκ.le (by rw [max_eq_left hω.le]; exact hω)
  rwa [max_eq_left hω.le] at h

theorem layerCake_eq_max {ω κ : ℝ} (hω : 0 < ω) (hκ : 0 < κ) :
    ω / κ + ω * ∫ t in (0 : ℝ)..κ, softKernel ω t = max 1 (ω / κ) := by
  rw [integral_softKernel_zero hω hκ]
  split_ifs with h
  · have h1 : ω / κ ≤ 1 := by rw [div_le_one hκ]; exact h.le
    rw [max_eq_left h1]
    field_simp
    ring
  · have h1 : 1 ≤ ω / κ := by rw [le_div_iff₀ hκ]; linarith
    rw [max_eq_right h1]
    ring

theorem one_le_layerCake {ω κ : ℝ} (hω : 0 < ω) (hκ : 0 < κ) :
    1 ≤ ω / κ + ω * ∫ t in (0 : ℝ)..κ, softKernel ω t := by
  rw [layerCake_eq_max hω hκ]
  exact le_max_left _ _

theorem integral_softKernel_Ioc {ω κ κ₀ : ℝ} (hκ : 0 < κ) (hκ₀ : κ < κ₀) :
    ∫ t in κ..κ₀, softKernel ω t = if max ω κ < κ₀ then 1 / max ω κ - 1 / κ₀ else 0 :=
  integral_softKernel hκ₀.le (lt_max_of_lt_right hκ)

theorem layerCake_hard_eq_one {ω κ κ₀ : ℝ} (hκ : 0 < κ) (h1 : κ ≤ ω) (h2 : ω < κ₀) :
    ω / κ₀ + ω * ∫ t in κ..κ₀, softKernel ω t = 1 := by
  have hω : 0 < ω := hκ.trans_le h1
  have hκ₀ : 0 < κ₀ := hω.trans h2
  rw [integral_softKernel_Ioc hκ (h1.trans_lt h2), max_eq_left h1]
  simp only [h2, ↓reduceIte]
  field_simp
  ring

theorem indicator_ge_le_layerCake {ω κ κ₀ : ℝ} (hω : 0 ≤ ω) (hκ : 0 < κ) (hκ₀ : κ < κ₀) :
    (if κ ≤ ω then (1 : ℝ) else 0) ≤ ω / κ₀ + ω * ∫ t in κ..κ₀, softKernel ω t := by
  have hpos : 0 < κ₀ := hκ.trans hκ₀
  have hint : 0 ≤ ∫ t in κ..κ₀, softKernel ω t :=
    intervalIntegral.integral_nonneg hκ₀.le (fun t _ => softKernel_nonneg ω t)
  split_ifs with h
  · rcases lt_or_ge ω κ₀ with h2 | h2
    · exact (layerCake_hard_eq_one hκ h h2).ge
    · have h3 : 1 ≤ ω / κ₀ := by rw [le_div_iff₀ hpos]; linarith
      nlinarith [mul_nonneg hω hint]
  · have h3 : 0 ≤ ω / κ₀ := div_nonneg hω hpos.le
    nlinarith [mul_nonneg hω hint]

theorem integral_softKernel_le {ω κ : ℝ} (hω : 0 < ω) (hκ : 0 < κ) :
    ∫ t in (0 : ℝ)..κ, softKernel ω t ≤ if ω < κ then 1 / ω else 0 := by
  rw [integral_softKernel_zero hω hκ]
  split_ifs with h
  · have : 0 ≤ 1 / κ := by positivity
    linarith
  · exact le_rfl

theorem measurable_softKernel (ω : ℝ) : Measurable (softKernel ω) := by
  unfold softKernel
  exact Measurable.indicator (by fun_prop) measurableSet_Ioi

theorem softKernel_le (ω : ℝ) (hω : 0 < ω) (t : ℝ) : softKernel ω t ≤ 1 / ω ^ 2 := by
  rcases lt_or_ge ω t with h | h
  · rw [softKernel_of_lt h]
    have : ω ^ 2 ≤ t ^ 2 := by nlinarith
    exact one_div_le_one_div_of_le (by positivity) this
  · rw [softKernel_of_le h]
    positivity

theorem integrableOn_softKernel {ω : ℝ} (hω : 0 < ω) (c κ : ℝ) :
    IntegrableOn (softKernel ω) (Ioc c κ) := by
  refine IntegrableOn.of_bound measure_Ioc_lt_top
    (measurable_softKernel ω).aestronglyMeasurable (1 / ω ^ 2) (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (softKernel_nonneg ω t)]
  exact softKernel_le ω hω t

theorem lintegral_softKernel {ω κ : ℝ} (hω : 0 < ω) (hκ : 0 < κ) :
    ∫⁻ t in Ioc 0 κ, ENNReal.ofReal (softKernel ω t)
      = ENNReal.ofReal (if ω < κ then 1 / ω - 1 / κ else 0) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_softKernel hω 0 κ)
    (ae_of_all _ fun t => softKernel_nonneg ω t), ← intervalIntegral.integral_of_le hκ.le,
    integral_softKernel_zero hω hκ]

theorem measurable_softKernel_uncurry {Ω : Type*} [MeasurableSpace Ω] {ω : Ω → ℝ}
    (hω : Measurable ω) : Measurable (fun p : ℝ × Ω => softKernel (ω p.2) p.1) := by
  have h : (fun p : ℝ × Ω => softKernel (ω p.2) p.1)
      = {p : ℝ × Ω | ω p.2 < p.1}.indicator (fun p => 1 / p.1 ^ 2) := by
    funext p
    by_cases hp : ω p.2 < p.1
    · rw [softKernel_of_lt hp, indicator_of_mem (by exact hp)]
    · rw [softKernel_of_le (not_lt.mp hp), indicator_of_notMem (by exact hp)]
  rw [h]
  exact Measurable.indicator (by fun_prop)
    (measurableSet_lt (hω.comp measurable_snd) measurable_fst)

theorem tonelli_infrared_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {ω : Ω → ℝ} (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)
    {w : Ω → ENNReal} (hw : Measurable w) {κ : ℝ} (hκ : 0 < κ) :
    ∫⁻ t in Ioc 0 κ, (∫⁻ x in {x | ω x < t}, w x ∂μ) * ENNReal.ofReal (1 / t ^ 2)
      = ∫⁻ x in {x | ω x < κ}, w x * ENNReal.ofReal (1 / ω x - 1 / κ) ∂μ := by
  have hmeas : ∀ t : ℝ, MeasurableSet {x | ω x < t} := fun t => measurableSet_lt hω measurable_const
  -- rewrite the inner integral with the kernel
  have h1 : ∀ t : ℝ, (∫⁻ x in {x | ω x < t}, w x ∂μ) * ENNReal.ofReal (1 / t ^ 2)
      = ∫⁻ x, w x * ENNReal.ofReal (softKernel (ω x) t) ∂μ := by
    intro t
    rw [← lintegral_indicator (hmeas t), ← lintegral_mul_const _ (hw.indicator (hmeas t))]
    refine lintegral_congr fun x => ?_
    by_cases hx : ω x < t
    · rw [softKernel_of_lt hx, indicator_of_mem (by exact hx)]
    · rw [softKernel_of_le (not_lt.mp hx), indicator_of_notMem (by exact hx)]
      simp
  simp_rw [h1]
  rw [lintegral_lintegral_swap]
  · rw [← lintegral_indicator (hmeas κ)]
    refine lintegral_congr_ae (hpos.mono fun x hx => ?_)
    beta_reduce
    rw [lintegral_const_mul _ (measurable_softKernel (ω x)).ennreal_ofReal,
      lintegral_softKernel hx hκ]
    by_cases hxκ : ω x < κ
    · rw [indicator_of_mem (by exact hxκ)]
      simp only [hxκ, ↓reduceIte]
    · rw [indicator_of_notMem (by exact hxκ)]
      simp only [hxκ, ↓reduceIte, ENNReal.ofReal_zero, mul_zero]
  · exact ((hw.comp measurable_snd).mul
      (measurable_softKernel_uncurry hω).ennreal_ofReal).aemeasurable

theorem tonelli_infrared_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {ω : Ω → ℝ} (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)
    {w : Ω → ENNReal} (hw : Measurable w) {κ : ℝ} (hκ : 0 < κ) :
    ∫⁻ t in Ioc 0 κ, (∫⁻ x in {x | ω x < t}, w x ∂μ) * ENNReal.ofReal (1 / t ^ 2)
      ≤ ∫⁻ x in {x | ω x < κ}, w x * ENNReal.ofReal (1 / ω x) ∂μ := by
  rw [tonelli_infrared_eq μ hω hpos hw hκ]
  refine lintegral_mono fun x => ?_
  gcongr
  have : 0 ≤ 1 / κ := by positivity
  linarith

theorem lintegral_le_layerCake {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {ω : Ω → ℝ} (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)
    {n : Ω → ENNReal} (hn : Measurable n) {κ : ℝ} (hκ : 0 < κ) :
    ∫⁻ x, n x ∂μ ≤ ENNReal.ofReal (1 / κ) * ∫⁻ x, ENNReal.ofReal (ω x) * n x ∂μ
      + ∫⁻ t in Ioc 0 κ, (∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * n x ∂μ)
          * ENNReal.ofReal (1 / t ^ 2) := by
  have hwn : Measurable fun x => ENNReal.ofReal (ω x) * n x := hω.ennreal_ofReal.mul hn
  have hmeas : MeasurableSet {x | ω x < κ} := measurableSet_lt hω measurable_const
  rw [tonelli_infrared_eq μ hω hpos hwn hκ, ← lintegral_const_mul _ hwn,
    ← lintegral_indicator hmeas, ← lintegral_add_left (hwn.const_mul _)]
  refine lintegral_mono_ae (hpos.mono fun x hx => ?_)
  have hκ' : (0 : ℝ) ≤ 1 / κ := by positivity
  by_cases hxκ : ω x < κ
  · rw [indicator_of_mem (by exact hxκ)]
    have hdiff : 0 ≤ 1 / ω x - 1 / κ := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hx hxκ.le
    have h1 : 1 / κ * ω x + ω x * (1 / ω x - 1 / κ) = 1 := by
      field_simp
      ring
    have h2 : n x = ENNReal.ofReal (1 / κ * ω x + ω x * (1 / ω x - 1 / κ)) * n x := by
      rw [h1, ENNReal.ofReal_one, one_mul]
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hκ',
      ENNReal.ofReal_mul hx.le] at h2
    refine le_of_eq (h2.trans ?_)
    ring
  · rw [indicator_of_notMem (by exact hxκ), add_zero, ← mul_assoc, ← ENNReal.ofReal_mul hκ']
    have h1 : 1 ≤ 1 / κ * ω x := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hκ]
      linarith [not_lt.mp hxκ]
    calc n x = 1 * n x := (one_mul _).symm
      _ ≤ ENNReal.ofReal (1 / κ * ω x) * n x := by
          gcongr
          exact ENNReal.one_le_ofReal.mpr h1

theorem lintegral_sq_mul_inv_sq (κ : ℝ) :
    ∫⁻ t in Ioc 0 κ, ENNReal.ofReal (t ^ 2) * ENNReal.ofReal (1 / t ^ 2) = ENNReal.ofReal κ := by
  have h : EqOn (fun t : ℝ => ENNReal.ofReal (t ^ 2) * ENNReal.ofReal (1 / t ^ 2))
      (fun _ => 1) (Ioc 0 κ) := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    beta_reduce
    rw [← ENNReal.ofReal_mul (by positivity), mul_one_div_cancel (pow_ne_zero 2 ht0),
      ENNReal.ofReal_one]
  rw [setLIntegral_congr_fun measurableSet_Ioc h]
  simp

theorem photon_number_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {ω : Ω → ℝ} (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)
    {n w : Ω → ENNReal} (hn : Measurable n) (hw : Measurable w) {κ C : ℝ} (hκ : 0 < κ)
    (hq : ∀ t ∈ Ioc 0 κ, ∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * n x ∂μ
      ≤ ENNReal.ofReal C * (ENNReal.ofReal (t ^ 2) + ∫⁻ x in {x | ω x < t}, w x ∂μ)) :
    ∫⁻ x, n x ∂μ ≤ ENNReal.ofReal (1 / κ) * ∫⁻ x, ENNReal.ofReal (ω x) * n x ∂μ
      + (ENNReal.ofReal C * ENNReal.ofReal κ
        + ENNReal.ofReal C * ∫⁻ x in {x | ω x < κ}, w x * ENNReal.ofReal (1 / ω x) ∂μ) := by
  refine (lintegral_le_layerCake μ hω hpos hn hκ).trans ?_
  gcongr
  calc ∫⁻ t in Ioc 0 κ, (∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * n x ∂μ)
          * ENNReal.ofReal (1 / t ^ 2)
      ≤ ∫⁻ t in Ioc 0 κ, (ENNReal.ofReal C * (ENNReal.ofReal (t ^ 2) * ENNReal.ofReal (1 / t ^ 2))
          + ENNReal.ofReal C * ((∫⁻ x in {x | ω x < t}, w x ∂μ) * ENNReal.ofReal (1 / t ^ 2))) := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
        calc _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (t ^ 2) + ∫⁻ x in {x | ω x < t}, w x ∂μ)
              * ENNReal.ofReal (1 / t ^ 2) := by gcongr; exact hq t ht
          _ = _ := by ring
    _ = ENNReal.ofReal C * ENNReal.ofReal κ + ENNReal.ofReal C
          * ∫⁻ t in Ioc 0 κ, (∫⁻ x in {x | ω x < t}, w x ∂μ) * ENNReal.ofReal (1 / t ^ 2) := by
        rw [lintegral_add_left (by fun_prop), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_sq_mul_inv_sq κ]
    _ ≤ _ := by
        gcongr
        exact tonelli_infrared_le μ hω hpos hw hκ

/-- The zero-excess soft-energy bound forces finite full photon number,
without assuming it beforehand. This applies to the analytic profile of an
exact optimizer once its soft-removal comparison has been proved. -/
theorem photon_number_finite_of_soft_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {ω : Ω → ℝ} (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)
    {n w : Ω → ENNReal} (hn : Measurable n) (hw : Measurable w)
    (henergy : ∫⁻ x, ENNReal.ofReal (ω x) * n x ∂μ < ⊤)
    (hweighted : ∫⁻ x, w x * ENNReal.ofReal (1 / ω x) ∂μ < ⊤)
    {κ C : ℝ} (hκ : 0 < κ)
    (hq : ∀ t ∈ Ioc 0 κ, ∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * n x ∂μ
      ≤ ENNReal.ofReal C * (ENNReal.ofReal (t ^ 2) + ∫⁻ x in {x | ω x < t}, w x ∂μ)) :
    ∫⁻ x, n x ∂μ < ⊤ := by
  apply lt_of_le_of_lt (photon_number_le μ hω hpos hn hw hκ hq)
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top henergy
  · apply ENNReal.add_lt_top.mpr
    constructor
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hweighted)

theorem integral_soft_profile_le {κ κ₀ d C a2 : ℝ} (hκ : 0 < κ) (hκ₀ : κ < κ₀)
    {s B : ℝ → ℝ} (hsm : Measurable s)
    (hs0 : ∀ t ∈ Ioc κ κ₀, 0 ≤ s t) (hB0 : ∀ t ∈ Ioc 0 κ₀, 0 ≤ B t)
    (hsB : ∀ t ∈ Ioc κ κ₀, s t ≤ 2 * d + C * (t ^ 2 + B t))
    (hBint : IntegrableOn (fun t => B t / t ^ 2) (Ioc 0 κ₀))
    (hBa : ∫ t in (0 : ℝ)..κ₀, B t / t ^ 2 ≤ a2) (hC : 0 ≤ C) :
    ∫ t in κ..κ₀, s t / t ^ 2 ≤ 2 * d * (1 / κ - 1 / κ₀) + C * (κ₀ - κ) + C * a2 := by
  have hκ₀pos : 0 < κ₀ := hκ.trans hκ₀
  have hBI0 : IntervalIntegrable (fun t => B t / t ^ 2) volume 0 κ₀ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hκ₀pos.le).mpr hBint
  have hBI : IntervalIntegrable (fun t => B t / t ^ 2) volume κ κ₀ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hκ₀.le).mpr
      (hBint.mono_set (Ioc_subset_Ioc_left hκ.le))
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume κ κ₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hκ₀.le]
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (hκ.trans_le ht.1).ne')
  have h1 : IntervalIntegrable (fun t : ℝ => 2 * d * (1 / t ^ 2)) volume κ κ₀ :=
    hinv.const_mul _
  have h2 : IntervalIntegrable (fun _ : ℝ => C) volume κ κ₀ := intervalIntegrable_const
  have h3 : IntervalIntegrable (fun t : ℝ => C * (B t / t ^ 2)) volume κ κ₀ := hBI.const_mul _
  have hG := (h1.add h2).add h3
  have hle : ∀ t ∈ Ioc κ κ₀, s t / t ^ 2 ≤ 2 * d * (1 / t ^ 2) + C + C * (B t / t ^ 2) := by
    intro t ht
    have ht0 : 0 < t := hκ.trans ht.1
    have := div_le_div_of_nonneg_right (hsB t ht) (by positivity : (0 : ℝ) ≤ t ^ 2)
    calc s t / t ^ 2 ≤ (2 * d + C * (t ^ 2 + B t)) / t ^ 2 := this
      _ = 2 * d * (1 / t ^ 2) + C + C * (B t / t ^ 2) := by
          field_simp
          ring
  have hsI : IntervalIntegrable (fun t => s t / t ^ 2) volume κ κ₀ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hκ₀.le]
    refine Integrable.mono' ((intervalIntegrable_iff_integrableOn_Ioc_of_le hκ₀.le).mp hG)
      (hsm.div (measurable_id.pow_const 2)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
    have ht0 : 0 < t := hκ.trans ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hs0 t ht) (by positivity))]
    exact hle t ht
  have hmono : ∫ t in κ..κ₀, s t / t ^ 2
      ≤ ∫ t in κ..κ₀, (2 * d * (1 / t ^ 2) + C + C * (B t / t ^ 2)) := by
    rw [intervalIntegral.integral_of_le hκ₀.le, intervalIntegral.integral_of_le hκ₀.le]
    exact setIntegral_mono_on hsI.1 hG.1 measurableSet_Ioc hle
  have hBmono : ∫ t in κ..κ₀, B t / t ^ 2 ≤ ∫ t in (0 : ℝ)..κ₀, B t / t ^ 2 := by
    refine intervalIntegral.integral_mono_interval hκ.le hκ₀.le le_rfl ?_ hBI0
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
    exact div_nonneg (hB0 t ht) (by positivity)
  have hval : ∫ t in κ..κ₀, (2 * d * (1 / t ^ 2) + C + C * (B t / t ^ 2))
      = 2 * d * (1 / κ - 1 / κ₀) + C * (κ₀ - κ) + C * ∫ t in κ..κ₀, B t / t ^ 2 := by
    rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, integral_one_div_sq hκ hκ₀.le, smul_eq_mul]
    ring
  have := mul_le_mul_of_nonneg_left (hBmono.trans hBa) hC
  linarith

theorem number_bound_assembly {N F κ κ₀ d C a2 I : ℝ} (hκ : 0 < κ) (hκ₀ : κ < κ₀)
    (hd : 0 ≤ d) (hC : 0 ≤ C) (hN : N ≤ F / κ₀ + I)
    (hI : I ≤ 2 * d * (1 / κ - 1 / κ₀) + C * (κ₀ - κ) + C * a2) :
    N ≤ F / κ₀ + 2 * d / κ + C * (κ₀ + a2) := by
  have h1 : 0 ≤ 2 * d * (1 / κ₀) := by
    have := hκ.trans hκ₀
    positivity
  have h2 : 0 ≤ C * κ := mul_nonneg hC hκ.le
  have h3 : 2 * d * (1 / κ - 1 / κ₀) = 2 * d / κ - 2 * d * (1 / κ₀) := by ring
  nlinarith

theorem uniform_number_bound {N F κ₀ C a2 : ℝ} (hF : 0 ≤ F)
    (hN : N ≤ F / κ₀ + C * (κ₀ + a2)) :
    N ≤ max (1 / κ₀) (C * (κ₀ + a2)) * (1 + F) := by
  set M := max (1 / κ₀) (C * (κ₀ + a2)) with hM
  have h1 : 1 / κ₀ ≤ M := le_max_left _ _
  have h2 : C * (κ₀ + a2) ≤ M := le_max_right _ _
  have h3 : F / κ₀ ≤ M * F := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 hF
  nlinarith

end LayerCake
end GptLean
