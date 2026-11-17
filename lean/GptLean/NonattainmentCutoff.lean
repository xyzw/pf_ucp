import GptLean.PhysicalArticleCutoff
import GptLean.NonattainmentScales

/-!
Cutoff moduli and ultraviolet tails for the thin-loop construction.

The two moduli are defined by the actual article cutoff integrals. Dominated
convergence proves their continuity at zero using only the two moments in
`ArticleCutoff`. No derivative or higher ultraviolet moment is required.
These results select the narrow axes and prove the vanishing scalar error in
the mixed trial-state estimate. They do not construct that trial state.
-/

noncomputable section

namespace GptLean.Nonattainment

open MeasureTheory Filter Topology Gaussian PhysicalPolarization

set_option Elab.async false
set_option maxHeartbeats 400000

section Dominated

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {ω w : X → ℝ}

/-- A bounded frequency multiplier, extended evenly to negative length scales. -/
def cutoffMultiplier (ω : X → ℝ) (ℓ : ℝ) (x : X) : ℝ :=
  min 1 (|ℓ| * |ω x|)

omit [MeasurableSpace X] in
theorem cutoffMultiplier_nonneg (ω : X → ℝ) (ℓ : ℝ) (x : X) :
    0 ≤ cutoffMultiplier ω ℓ x :=
  le_min (by norm_num) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

omit [MeasurableSpace X] in
theorem cutoffMultiplier_sq_le_one (ω : X → ℝ) (ℓ : ℝ) (x : X) :
    cutoffMultiplier ω ℓ x ^ 2 ≤ 1 := by
  have h0 := cutoffMultiplier_nonneg ω ℓ x
  have h1 : cutoffMultiplier ω ℓ x ≤ 1 := min_le_left _ _
  nlinarith

/-- The squared modulus is continuous for any integrable nonnegative weight. -/
theorem continuous_cutoff_integral (hω : Measurable ω) (hw : Integrable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) :
    Continuous (fun ℓ : ℝ => ∫ x, cutoffMultiplier ω ℓ x ^ 2 * w x ∂μ) := by
  apply continuous_of_dominated (bound := w)
  · intro ℓ
    have hωabs : Measurable (fun x => |ω x|) := by
      simpa only [Real.norm_eq_abs] using hω.norm
    have hm : Measurable (fun x => cutoffMultiplier ω ℓ x ^ 2) :=
      (measurable_const.min (measurable_const.mul hωabs)).pow_const 2
    exact hm.aestronglyMeasurable.mul hw.aestronglyMeasurable
  · intro ℓ
    filter_upwards [hw0] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hx)]
    exact (mul_le_mul_of_nonneg_right (cutoffMultiplier_sq_le_one ω ℓ x) hx).trans_eq
      (one_mul _)
  · exact hw
  · exact ae_of_all _ fun x => by
      unfold cutoffMultiplier
      fun_prop

theorem cutoff_integral_tendsto_zero (hω : Measurable ω) (hw : Integrable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) :
    Tendsto (fun ℓ : ℝ => ∫ x, cutoffMultiplier ω ℓ x ^ 2 * w x ∂μ)
      (𝓝 0) (𝓝 0) := by
  simpa [cutoffMultiplier] using (continuous_cutoff_integral hω hw hw0).tendsto 0

/-- Every integrable weight has a vanishing high-frequency tail. -/
theorem cutoff_tail_tendsto_zero (hω : Measurable ω) (hw : Integrable w μ) :
    Tendsto (fun K : ℝ => ∫ x in {x | K ≤ ω x}, w x ∂μ) atTop (𝓝 0) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence (fun x => ‖w x‖)
    (Eventually.of_forall fun K : ℝ => hw.aestronglyMeasurable.indicator
      (measurableSet_le measurable_const hω))
    (Eventually.of_forall fun K : ℝ => ae_of_all μ fun x =>
      norm_indicator_le_norm_self _ _)
    hw.norm
    (ae_of_all μ fun x => show
      Tendsto (fun K : ℝ => {y | K ≤ ω y}.indicator w x) atTop (𝓝 0) from
      tendsto_const_nhds.congr' ((eventually_gt_atTop (ω x)).mono fun K hK => by
        simp [not_le.mpr hK]))
  simpa only [integral_indicator (measurableSet_le measurable_const hω), integral_zero]
    using hlim

end Dominated

/-- The weight for the ordinary or inverse-frequency cutoff moment. -/
def cutoffWeight (χ : ArticleCutoff) (infrared : Bool) (k : FieldSpace) : ℝ :=
  if infrared then (1 / ‖k‖) * ‖χ.value k‖ ^ 2 else ‖χ.value k‖ ^ 2

theorem cutoffWeight_integrable (χ : ArticleCutoff) (infrared : Bool) :
    Integrable (cutoffWeight χ infrared) volume := by
  cases infrared
  · exact χ.ultraviolet
  · exact χ.infrared

theorem cutoffWeight_nonneg (χ : ArticleCutoff) (infrared : Bool) (k : FieldSpace) :
    0 ≤ cutoffWeight χ infrared k := by
  cases infrared <;> simp only [cutoffWeight, Bool.false_eq_true, ↓reduceIte]
  · positivity
  · positivity

/-- `d₀` and `d₁` from Step 2, with an even extension in the scale. -/
def cutoffModulus (χ : ArticleCutoff) (infrared : Bool) (ℓ : ℝ) : ℝ :=
  Real.sqrt (∫ k, cutoffMultiplier (fun k : FieldSpace => ‖k‖) ℓ k ^ 2 *
    cutoffWeight χ infrared k)

theorem cutoffModulus_nonneg (χ : ArticleCutoff) (infrared : Bool) (ℓ : ℝ) :
    0 ≤ cutoffModulus χ infrared ℓ := Real.sqrt_nonneg _

theorem cutoffModulus_tendsto_zero (χ : ArticleCutoff) (infrared : Bool) :
    Tendsto (cutoffModulus χ infrared) (𝓝 0) (𝓝 0) := by
  change Tendsto (fun ℓ : ℝ => Real.sqrt (∫ k : FieldSpace,
    cutoffMultiplier (fun k : FieldSpace => ‖k‖) ℓ k ^ 2 * cutoffWeight χ infrared k))
      (𝓝 0) (𝓝 0)
  simpa only [Real.sqrt_zero] using
    (cutoff_integral_tendsto_zero measurable_norm (cutoffWeight_integrable χ infrared)
      (ae_of_all _ (cutoffWeight_nonneg χ infrared))).sqrt

/-- The actual cutoff assumptions suffice to choose each narrow ellipse axis. -/
theorem exists_cutoff_thin_axis (χ : ArticleCutoff) {b : ℝ} (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧ a ≤ b ^ 3 ∧
      cutoffModulus χ false (2 * a) + cutoffModulus χ true (2 * a) ≤ b ^ 2 :=
  exists_thin_axis ((cutoffModulus_tendsto_zero χ false).mono_left nhdsWithin_le_nhds)
    ((cutoffModulus_tendsto_zero χ true).mono_left nhdsWithin_le_nhds) hb

/-- The error on the right of the mixed-state upper bound. -/
def trialError (χ : ArticleCutoff) (e b : ℝ) : ℝ :=
  e ^ 2 * (4 * cutoffModulus χ false (3 * b) ^ 2 +
    (∫ k in {k : FieldSpace | b⁻¹ ≤ ‖k‖}, ‖χ.value k‖ ^ 2) +
    9 * b * ∫ k, ‖χ.value k‖ ^ 2)

theorem trialError_tendsto_zero (χ : ArticleCutoff) (e : ℝ) :
    Tendsto (trialError χ e) (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun b : ℝ => b) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hm : Tendsto (fun b : ℝ => cutoffModulus χ false (3 * b))
      (𝓝[>] 0) (𝓝 0) :=
    (cutoffModulus_tendsto_zero χ false).comp
      (by simpa using hid.const_mul (3 : ℝ))
  have ht : Tendsto (fun b : ℝ => ∫ k in {k : FieldSpace | b⁻¹ ≤ ‖k‖},
      ‖χ.value k‖ ^ 2) (𝓝[>] 0) (𝓝 0) :=
    (cutoff_tail_tendsto_zero measurable_norm χ.ultraviolet).comp
      tendsto_inv_nhdsGT_zero
  have hb : Tendsto (fun b : ℝ => 9 * b * ∫ k, ‖χ.value k‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (hid.const_mul (9 : ℝ)).mul_const
      (∫ k, ‖χ.value k‖ ^ 2)
  change Tendsto (fun b : ℝ => e ^ 2 * (4 * cutoffModulus χ false (3 * b) ^ 2 +
    (∫ k in {k : FieldSpace | b⁻¹ ≤ ‖k‖}, ‖χ.value k‖ ^ 2) +
    9 * b * ∫ k, ‖χ.value k‖ ^ 2)) (𝓝[>] 0) (𝓝 0)
  simpa only [zero_pow two_ne_zero, mul_zero, zero_add] using
    ((((hm.pow 2).const_mul 4).add ht).add hb).const_mul (e ^ 2)

end GptLean.Nonattainment
