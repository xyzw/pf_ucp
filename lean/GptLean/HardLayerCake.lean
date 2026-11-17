/-
Adapted from the repository's claude_lean/QEDFT/Attainment/HardLayerCake.lean.
The mathematical proof bodies are retained and rechecked independently under
GptLean. No QEDFT modules are imported.
-/
import GptLean.LayerCake
import GptLean.CutoffProfile
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Integrated hard-photon number control for `thm-unrestricted-attainment`.

`tonelli_hard_eq` proves the Tonelli identity over the interval `(κ, κ₀]`.
`lintegral_hard_le_layerCake` proves the corresponding hard-photon inequality
for extended nonnegative Lebesgue integrals. `numHard_le_of_density` converts
it to the real-valued interval integral used before
`unrestricted-near-minimizer-number`, proving the required integrability.

`HasPhotonDensity` is an explicit moment-representation interface. It is not a
proof of the Pauli–Fierz trace-to-momentum-density correspondence. It assumes
finite radiation energy and exact moment identities, while allowing the full
photon density to have infinite total mass. Hard-photon moments at positive
cutoff are controlled by the derived inequality.
-/

namespace GptLean.HardLayerCake

open MeasureTheory Set Filter
open scoped ENNReal
open GptLean.LayerCake

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
  {ω : Ω → ℝ} (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)

theorem lintegral_softKernel_Ioc {ω κ κ₀ : ℝ} (hω : 0 < ω) (hκ : 0 < κ) (hκ₀ : κ < κ₀) :
    ∫⁻ t in Ioc κ κ₀, ENNReal.ofReal (softKernel ω t)
      = ENNReal.ofReal (if max ω κ < κ₀ then 1 / max ω κ - 1 / κ₀ else 0) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_softKernel hω κ κ₀)
    (ae_of_all _ fun t => softKernel_nonneg ω t), ← intervalIntegral.integral_of_le hκ₀.le,
    integral_softKernel_Ioc hκ hκ₀]

include hω hpos in

theorem tonelli_hard_eq {w : Ω → ℝ≥0∞} (hw : Measurable w) {κ κ₀ : ℝ} (hκ : 0 < κ)
    (hκ₀ : κ < κ₀) :
    ∫⁻ t in Ioc κ κ₀, (∫⁻ x in {x | ω x < t}, w x ∂μ) * ENNReal.ofReal (1 / t ^ 2)
      = ∫⁻ x in {x | ω x < κ₀}, w x * ENNReal.ofReal (1 / max (ω x) κ - 1 / κ₀) ∂μ := by
  have hmeas : ∀ t : ℝ, MeasurableSet {x | ω x < t} := fun t =>
    measurableSet_lt hω measurable_const
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
  · rw [← lintegral_indicator (hmeas κ₀)]
    refine lintegral_congr_ae (hpos.mono fun x hx => ?_)
    beta_reduce
    rw [lintegral_const_mul _ (measurable_softKernel (ω x)).ennreal_ofReal,
      lintegral_softKernel_Ioc hx hκ hκ₀]
    by_cases hxκ : ω x < κ₀
    · rw [indicator_of_mem (by exact hxκ)]
      have : max (ω x) κ < κ₀ := max_lt hxκ hκ₀
      simp only [this, ↓reduceIte]
    · rw [indicator_of_notMem (by exact hxκ)]
      have : ¬ max (ω x) κ < κ₀ := fun h => hxκ (lt_of_le_of_lt (le_max_left _ _) h)
      simp only [this, ↓reduceIte, ENNReal.ofReal_zero, mul_zero]
  · exact ((hw.comp measurable_snd).mul
      (measurable_softKernel_uncurry hω).ennreal_ofReal).aemeasurable

include hω hpos in

theorem lintegral_hard_le_layerCake {n : Ω → ℝ≥0∞} (hn : Measurable n) {κ κ₀ : ℝ} (hκ : 0 < κ)
    (hκ₀ : κ < κ₀) :
    ∫⁻ x in {x | κ ≤ ω x}, n x ∂μ
      ≤ ENNReal.ofReal (1 / κ₀) * ∫⁻ x, ENNReal.ofReal (ω x) * n x ∂μ
        + ∫⁻ t in Ioc κ κ₀, (∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * n x ∂μ)
            * ENNReal.ofReal (1 / t ^ 2) := by
  have hwn : Measurable fun x => ENNReal.ofReal (ω x) * n x := hω.ennreal_ofReal.mul hn
  have hmeas : MeasurableSet {x | ω x < κ₀} := measurableSet_lt hω measurable_const
  have hmeas' : MeasurableSet {x | κ ≤ ω x} := measurableSet_le measurable_const hω
  rw [tonelli_hard_eq μ hω hpos hwn hκ hκ₀, ← lintegral_const_mul _ hwn,
    ← lintegral_indicator hmeas, ← lintegral_add_left (hwn.const_mul _),
    ← lintegral_indicator hmeas']
  refine lintegral_mono_ae (hpos.mono fun x hx => ?_)
  have hκ₀' : (0 : ℝ) ≤ 1 / κ₀ := by
    have : 0 < κ₀ := hκ.trans hκ₀
    positivity
  by_cases hxκ : κ ≤ ω x
  · rw [indicator_of_mem (by exact hxκ)]
    by_cases hxκ₀ : ω x < κ₀
    · rw [indicator_of_mem (by exact hxκ₀), max_eq_left hxκ]
      have hdiff : 0 ≤ 1 / ω x - 1 / κ₀ := by
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le hx hxκ₀.le
      have h1 : 1 / κ₀ * ω x + ω x * (1 / ω x - 1 / κ₀) = 1 := by
        field_simp
        ring
      have h2 : n x = ENNReal.ofReal (1 / κ₀ * ω x + ω x * (1 / ω x - 1 / κ₀)) * n x := by
        rw [h1, ENNReal.ofReal_one, one_mul]
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hκ₀',
        ENNReal.ofReal_mul hx.le] at h2
      refine le_of_eq (h2.trans ?_)
      ring
    · rw [indicator_of_notMem (by exact hxκ₀), add_zero, ← mul_assoc,
        ← ENNReal.ofReal_mul hκ₀']
      have h1 : 1 ≤ 1 / κ₀ * ω x := by
        have : 0 < κ₀ := hκ.trans hκ₀
        rw [one_div, inv_mul_eq_div, le_div_iff₀ this]
        linarith [not_lt.mp hxκ₀]
      calc n x = 1 * n x := (one_mul _).symm
        _ ≤ ENNReal.ofReal (1 / κ₀ * ω x) * n x := by
            gcongr
            exact ENNReal.one_le_ofReal.mpr h1
  · rw [indicator_of_notMem (by exact hxκ)]
    exact bot_le

structure HasPhotonDensity (ω : Ω → ℝ) (n : Ω → ℝ≥0∞) (numHard : ℝ → ℝ) (Esoft : ℝ → ℝ)
    (Erad : ℝ) : Prop where
  measurable : Measurable n
  finite : ∫⁻ x, ENNReal.ofReal (ω x) * n x ∂μ < ⊤
  numHard_eq : ∀ κ, numHard κ = (∫⁻ x in {x | κ ≤ ω x}, n x ∂μ).toReal
  Esoft_eq : ∀ t, Esoft t = (∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * n x ∂μ).toReal
  Erad_eq : Erad = (∫⁻ x, ENNReal.ofReal (ω x) * n x ∂μ).toReal

include hω hpos in

theorem numHard_le_of_density {n : Ω → ℝ≥0∞} {numHard Esoft : ℝ → ℝ} {Erad Een : ℝ}
    (h : HasPhotonDensity μ ω n numHard Esoft Erad) (hrad : Erad ≤ Een)
    {κ κ₀ : ℝ} (hκ : 0 < κ) (hκ₀ : κ < κ₀) :
    numHard κ ≤ Een / κ₀ + ∫ t in κ..κ₀, Esoft t / t ^ 2 := by
  have hpos₀ : 0 < κ₀ := hκ.trans hκ₀
  have hwn : Measurable fun x => ENNReal.ofReal (ω x) * n x := hω.ennreal_ofReal.mul h.measurable
  -- finiteness of the soft energies
  have hfin : ∀ t, ∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * n x ∂μ ≠ ⊤ := fun t =>
    (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) h.finite).ne
  -- the `t`-integrand as an `ofReal`
  have hpt : ∀ t ∈ Ioc κ κ₀, ENNReal.ofReal (Esoft t / t ^ 2)
      = (∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * n x ∂μ) * ENNReal.ofReal (1 / t ^ 2) := by
    intro t _
    rw [h.Esoft_eq t, div_eq_mul_one_div, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hfin t)]
  -- measurability of `t ↦ Esoft t` (monotone) and nonnegativity
  have hEmono : Monotone Esoft := fun s t hst => by
    rw [h.Esoft_eq s, h.Esoft_eq t]
    exact ENNReal.toReal_mono (hfin t) (lintegral_mono_set fun _ hx => lt_of_lt_of_le hx hst)
  have hEnn : ∀ t, 0 ≤ Esoft t / t ^ 2 := fun t => by
    rw [h.Esoft_eq t]; exact div_nonneg ENNReal.toReal_nonneg (sq_nonneg t)
  have hmeasE : Measurable fun t => Esoft t / t ^ 2 :=
    hEmono.measurable.div (measurable_id.pow_const 2)
  -- the lintegral of the `t`-integrand is finite
  have hbound : ∫⁻ t in Ioc κ κ₀, ENNReal.ofReal (Esoft t / t ^ 2) < ⊤ := by
    rw [setLIntegral_congr_fun measurableSet_Ioc hpt]
    calc ∫⁻ t in Ioc κ κ₀, (∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * n x ∂μ)
          * ENNReal.ofReal (1 / t ^ 2)
        ≤ ∫⁻ t in Ioc κ κ₀, (∫⁻ x, ENNReal.ofReal (ω x) * n x ∂μ) * ENNReal.ofReal (1 / κ ^ 2) := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
          refine mul_le_mul' (setLIntegral_le_lintegral _ _) (ENNReal.ofReal_le_ofReal ?_)
          exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hκ.le ht.1.le 2)
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top h.finite ENNReal.ofReal_lt_top)
            (measure_Ioc_lt_top)
  -- integrability and the identification of the Bochner integral
  have hint : IntegrableOn (fun t => Esoft t / t ^ 2) (Ioc κ κ₀) := by
    refine ⟨hmeasE.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hEnn)]
    exact hbound
  have hInt : ∫ t in κ..κ₀, Esoft t / t ^ 2
      = (∫⁻ t in Ioc κ κ₀, (∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * n x ∂μ)
          * ENNReal.ofReal (1 / t ^ 2)).toReal := by
    rw [intervalIntegral.integral_of_le hκ₀.le,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hEnn) hmeasE.aestronglyMeasurable,
      setLIntegral_congr_fun measurableSet_Ioc hpt]
  -- assemble
  have key := lintegral_hard_le_layerCake μ hω hpos h.measurable hκ hκ₀ (n := n)
  have hRfin : ENNReal.ofReal (1 / κ₀) * ∫⁻ x, ENNReal.ofReal (ω x) * n x ∂μ
      + ∫⁻ t in Ioc κ κ₀, (∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * n x ∂μ)
          * ENNReal.ofReal (1 / t ^ 2) ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨(ENNReal.mul_lt_top ENNReal.ofReal_lt_top h.finite).ne, ?_⟩
    rw [← setLIntegral_congr_fun measurableSet_Ioc hpt]
    exact hbound.ne
  have hmono := ENNReal.toReal_mono hRfin key
  rw [h.numHard_eq κ, hInt]
  refine hmono.trans ?_
  rw [ENNReal.toReal_add (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h.finite).ne
    (by rw [← setLIntegral_congr_fun measurableSet_Ioc hpt]; exact hbound.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← h.Erad_eq]
  have h1 : Erad / κ₀ ≤ Een / κ₀ := div_le_div_of_nonneg_right hrad hpos₀.le
  have h2 : 1 / κ₀ * Erad = Erad / κ₀ := by ring
  linarith

include hω hpos in
/-- The current `unrestricted-near-minimizer-number` inequality from a photon
moment representation and the current soft-energy profile bound. The cutoff
profile's integrability and integral bound are explicit analytic hypotheses.
They can be proved by the Tonelli theorems in `GptLean.LayerCake`. -/
theorem numHard_le_of_soft_profile
    {n : Ω → ℝ≥0∞} {numHard Esoft B : ℝ → ℝ} {Erad Een κ κ₀ d C a2 : ℝ}
    (h : HasPhotonDensity μ ω n numHard Esoft Erad) (hrad : Erad ≤ Een)
    (hκ : 0 < κ) (hκ₀ : κ < κ₀) (hd : 0 ≤ d) (hC : 0 ≤ C)
    (hB0 : ∀ t ∈ Ioc 0 κ₀, 0 ≤ B t)
    (hBint : IntegrableOn (fun t => B t / t ^ 2) (Ioc 0 κ₀))
    (hBa : ∫ t in (0 : ℝ)..κ₀, B t / t ^ 2 ≤ a2)
    (hsoft : ∀ t ∈ Ioc κ κ₀, Esoft t ≤ 2 * d + C * (t ^ 2 + B t)) :
    numHard κ ≤ Een / κ₀ + 2 * d / κ + C * (κ₀ + a2) := by
  have hfin : ∀ t, ∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * n x ∂μ ≠ ⊤ :=
    fun t => (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) h.finite).ne
  have hmono : Monotone Esoft := fun s t hst => by
    rw [h.Esoft_eq s, h.Esoft_eq t]
    exact ENNReal.toReal_mono (hfin t)
      (lintegral_mono_set fun _ hx => lt_of_lt_of_le hx hst)
  have hnonneg : ∀ t ∈ Ioc κ κ₀, 0 ≤ Esoft t := by
    intro t _
    rw [h.Esoft_eq t]
    exact ENNReal.toReal_nonneg
  exact number_bound_assembly hκ hκ₀ hd hC
    (numHard_le_of_density μ hω hpos h hrad hκ hκ₀)
    (integral_soft_profile_le hκ hκ₀ hmono.measurable hnonneg hB0 hsoft hBint hBa hC)

include hω hpos in
/-- The complete integrated implication used for
`unrestricted-near-minimizer-number`, now with the actual Lebesgue cutoff
profile. The remaining paper-specific premise is `hsoft`, and `h` is the
trace-to-moment representation interface. Tonelli, profile integrability,
and the hard-photon integration are proved by the imported modules. -/
theorem numHard_le_of_infrared_profile
    {n w : Ω → ℝ≥0∞} {numHard Esoft : ℝ → ℝ} {Erad Een κ κ₀ d C : ℝ}
    (h : HasPhotonDensity μ ω n numHard Esoft Erad) (hrad : Erad ≤ Een)
    (hw : Measurable w)
    (hB : ∫⁻ x, w x ∂μ < ⊤)
    (hA : ∫⁻ x, w x * ENNReal.ofReal (1 / ω x) ∂μ < ⊤)
    (hκ : 0 < κ) (hκ₀ : κ < κ₀) (hd : 0 ≤ d) (hC : 0 ≤ C)
    (hsoft : ∀ t ∈ Ioc κ κ₀,
      Esoft t ≤ 2 * d + C * (t ^ 2 + GptLean.CutoffProfile.bsq μ ω w t)) :
    numHard κ ≤ Een / κ₀ + 2 * d / κ +
      C * (κ₀ + GptLean.CutoffProfile.asq μ ω w κ₀) := by
  exact numHard_le_of_soft_profile μ hω hpos h hrad hκ hκ₀ hd hC
    (fun t _ => GptLean.CutoffProfile.bsq_nonneg t)
    (GptLean.CutoffProfile.integrableOn_bsq_div_sq hω hpos hw hB hA (hκ.trans hκ₀))
    (GptLean.CutoffProfile.integral_bsq_div_sq_le hω hpos hw hB hA (hκ.trans hκ₀))
    hsoft

end GptLean.HardLayerCake
