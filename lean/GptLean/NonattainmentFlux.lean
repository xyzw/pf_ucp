import GptLean.NonattainmentKernel
import GptLean.NonattainmentEllipse

/-!
Cancellation of the actual field circulation on the two arms of the central
ellipse. Both weighted photon norms have the required cubic smallness after
the narrow-axis choice. The circulation is a Bochner integral of the actual
Fourier form factors, rather than a supplied flux estimate.
-/

noncomputable section

namespace GptLean.Nonattainment

open MeasureTheory Gaussian PhysicalFock PhysicalPolarization

set_option Elab.async false
set_option maxHeartbeats 400000

section LineIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ellipseFlux (A₀ A₁ : FieldSpace → E) (a b : ℝ) : E :=
  ∫ t in -(Real.pi / 2)..3 * Real.pi / 2,
    (-a * Real.sin t) • A₀ (ellipse a b t) +
      (b * Real.cos t) • A₁ (ellipse a b t)

theorem ellipseFlux_paired (A₀ A₁ : FieldSpace → E)
    (hA₀ : Continuous A₀) (hA₁ : Continuous A₁) (a b : ℝ) :
    ellipseFlux A₀ A₁ a b =
      ∫ t in -(Real.pi / 2)..Real.pi / 2,
        (-a * Real.sin t) •
          (A₀ (ellipse a b t) + A₀ (ellipse a b (Real.pi - t))) +
        (b * Real.cos t) •
          (A₁ (ellipse a b t) - A₁ (ellipse a b (Real.pi - t))) := by
  let f : ℝ → E := fun t => (-a * Real.sin t) • A₀ (ellipse a b t) +
    (b * Real.cos t) • A₁ (ellipse a b t)
  have hf : Continuous f := by
    exact ((continuous_const.mul Real.continuous_sin).smul
      (hA₀.comp (ellipse_continuous a b))).add
      ((continuous_const.mul Real.continuous_cos).smul
        (hA₁.comp (ellipse_continuous a b)))
  have href : (∫ t in Real.pi / 2..3 * Real.pi / 2, f t) =
      ∫ t in -(Real.pi / 2)..Real.pi / 2, f (Real.pi - t) := by
    have h := intervalIntegral.integral_comp_sub_left
      (a := -(Real.pi / 2)) (b := Real.pi / 2) f Real.pi
    convert h.symm using 1
    congr 1
    all_goals ring
  have hfr : Continuous (fun t : ℝ => f (Real.pi - t)) :=
    hf.comp (continuous_const.sub continuous_id)
  change (∫ t in -(Real.pi / 2)..3 * Real.pi / 2, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-(Real.pi / 2)) (Real.pi / 2))
    (hf.intervalIntegrable (Real.pi / 2) (3 * Real.pi / 2)), href,
    ← intervalIntegral.integral_add (hf.intervalIntegrable _ _)
      (hfr.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [f]
  rw [Real.sin_pi_sub, Real.cos_pi_sub]
  module

theorem ellipseFlux_norm_le (A₀ A₁ : FieldSpace → E)
    (hA₀ : Continuous A₀) (hA₁ : Continuous A₁)
    {a b M D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : ∀ x, ‖A₀ x‖ ≤ M)
    (hD : ∀ t, ‖A₁ (ellipse a b t) - A₁ (ellipse a b (Real.pi - t))‖ ≤ D) :
    ‖ellipseFlux A₀ A₁ a b‖ ≤ (2 * a * M + b * D) * Real.pi := by
  rw [ellipseFlux_paired A₀ A₁ hA₀ hA₁]
  have hp (t : ℝ) :
      ‖(-a * Real.sin t) •
          (A₀ (ellipse a b t) + A₀ (ellipse a b (Real.pi - t))) +
        (b * Real.cos t) •
          (A₁ (ellipse a b t) - A₁ (ellipse a b (Real.pi - t)))‖ ≤
        2 * a * M + b * D := by
    have hs : |-a * Real.sin t| ≤ a := by
      rw [abs_mul, abs_neg, abs_of_nonneg ha]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one t) ha).trans_eq (mul_one _)
    have hc : |b * Real.cos t| ≤ b := by
      rw [abs_mul, abs_of_nonneg hb]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) hb).trans_eq (mul_one _)
    have hsum : ‖A₀ (ellipse a b t) + A₀ (ellipse a b (Real.pi - t))‖ ≤ 2 * M :=
      (norm_add_le _ _).trans ((add_le_add (hM _) (hM _)).trans_eq (by ring))
    refine (norm_add_le _ _).trans ?_
    simp only [norm_smul, Real.norm_eq_abs]
    have h := add_le_add (mul_le_mul hs hsum (norm_nonneg _) ha)
      (mul_le_mul hc (hD t) (norm_nonneg _) hb)
    nlinarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(Real.pi / 2)) (b := Real.pi / 2) (fun t _ => hp t)
  have hlen : |Real.pi / 2 - -(Real.pi / 2)| = Real.pi := by
    rw [show Real.pi / 2 - -(Real.pi / 2) = Real.pi by ring, abs_of_pos Real.pi_pos]
  simpa only [hlen] using h

end LineIntegral

/-- The central field circulation in either of the two photon norms. -/
def centralFieldFlux (F : Frame) (χ : ArticleCutoff) (infrared : Bool) (a b : ℝ) :
    Lp ℂ 2 photonMeasure :=
  ellipseFlux (weightedFieldKernel F χ infrared 0)
    (weightedFieldKernel F χ infrared 1) a b

theorem centralFieldFlux_norm_le (F : Frame) (χ : ArticleCutoff) (infrared : Bool)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖centralFieldFlux F χ infrared a b‖ ≤
      2 * Real.pi * (a * cutoffMoment χ infrared +
        b * cutoffModulus χ infrared (2 * a)) := by
  have h := ellipseFlux_norm_le (weightedFieldKernel F χ infrared 0)
    (weightedFieldKernel F χ infrared 1)
    (weightedFieldKernel_continuous F χ infrared 0)
    (weightedFieldKernel_continuous F χ infrared 1) ha hb
    (weightedFieldKernel_norm_le F χ infrared 0)
    (fun t => (weightedFieldKernel_difference_le F χ infrared 1 _ _).trans
      (mul_le_mul_of_nonneg_left
        (cutoffModulus_mono χ infrared (norm_nonneg _)
          (ellipse_reflection_distance ha b t)) (by norm_num)))
  exact h.trans_eq (by ring)

theorem centralFieldFlux_cubic_bound (F : Frame) (χ : ArticleCutoff) (infrared : Bool)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b ^ 3)
    (hd : cutoffModulus χ infrared (2 * a) ≤ b ^ 2) :
    ‖centralFieldFlux F χ infrared a b‖ ≤
      (2 * Real.pi * (cutoffMoment χ infrared + 1)) * b ^ 3 := by
  refine (centralFieldFlux_norm_le F χ infrared ha hb).trans ?_
  have h₀ := mul_le_mul_of_nonneg_right hab (cutoffMoment_nonneg χ infrared)
  have h₁ := mul_le_mul_of_nonneg_left hd hb
  calc
    _ ≤ 2 * Real.pi * (b ^ 3 * cutoffMoment χ infrared + b * b ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add h₀ h₁) (by positivity)
    _ = _ := by ring

theorem centralFieldFlux_perimeter_bound (F : Frame) (χ : ArticleCutoff) (infrared : Bool)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b ^ 3)
    (hd : cutoffModulus χ infrared (2 * a) ≤ b ^ 2) :
    ‖centralFieldFlux F χ infrared a b‖ ≤
      (2 * Real.pi * (cutoffMoment χ infrared + 1)) * b * ellipsePerimeter a b ^ 2 := by
  refine (centralFieldFlux_cubic_bound F χ infrared ha hb hab hd).trans ?_
  have hL : b ≤ ellipsePerimeter a b := by
    linarith [four_mul_le_ellipsePerimeter a b]
  have hsq := pow_le_pow_left₀ hb hL 2
  have hM := cutoffMoment_nonneg χ infrared
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hb)
    (show 0 ≤ 2 * Real.pi * (cutoffMoment χ infrared + 1) by
      positivity)
  nlinarith

end GptLean.Nonattainment
