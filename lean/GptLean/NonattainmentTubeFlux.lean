import GptLean.NonattainmentFlux
import GptLean.NonattainmentTubeDifferential

/-!
Actual field circulation on the offset loops of the ellipse tube. The
comparison with the central loop uses the quantitative kernel modulus and
the proved curvature bound, uniformly over the transverse square.
-/

noncomputable section

namespace GptLean.Nonattainment

open MeasureTheory Gaussian PhysicalFock PhysicalPolarization

set_option Elab.async false
set_option maxHeartbeats 600000

theorem ellipse_norm_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (θ : ℝ) :
    ‖ellipse a b θ‖ ≤ b := by
  apply (sq_le_sq₀ (norm_nonneg _) (ha.trans hab)).mp
  have heq : ‖ellipse a b θ‖ ^ 2 =
      a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2 := by
    simp [ellipse, coordinateAxis, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, mul_pow]
  rw [heq]
  have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2) (sq_nonneg (Real.cos θ))
  nlinarith [congrArg (fun x : ℝ => b ^ 2 * x) (Real.sin_sq_add_cos_sq θ)]

theorem ellipseTubePoint_distance {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ r z : ℝ) :
    ‖ellipseTubePoint a b θ r z - ellipse a b θ‖ ≤ |r| + |z| := by
  have h : ellipseTubePoint a b θ r z - ellipse a b θ =
      r • ellipseNormal a b θ + z • coordinateAxis 2 := by
    unfold ellipseTubePoint
    abel
  rw [h]
  simpa only [norm_smul, ellipseNormal_norm ha hab, coordinateAxis_norm, mul_one,
    Real.norm_eq_abs] using norm_add_le (r • ellipseNormal a b θ) (z • coordinateAxis 2)

theorem ellipseTubePoint_norm_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ r z : ℝ) :
    ‖ellipseTubePoint a b θ r z‖ ≤ b + |r| + |z| := by
  calc
    ‖ellipseTubePoint a b θ r z‖ =
        ‖(ellipseTubePoint a b θ r z - ellipse a b θ) + ellipse a b θ‖ := by rw [sub_add_cancel]
    _ ≤ ‖ellipseTubePoint a b θ r z - ellipse a b θ‖ + ‖ellipse a b θ‖ := norm_add_le _ _
    _ ≤ (|r| + |z|) + b :=
      add_le_add (ellipseTubePoint_distance ha hab θ r z) (ellipse_norm_le ha.le hab θ)
    _ = _ := by ring

theorem ellipseTubeFactor_error {a b R θ r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : |r| ≤ R) :
    |ellipseTubeFactor a b θ r - 1| ≤ R * (b / a ^ 2) := by
  simp only [ellipseTubeFactor, sub_sub_cancel_left, abs_neg, abs_mul,
    abs_of_pos (ellipseCurvature_pos ha hab θ)]
  exact mul_le_mul hr (ellipseCurvature_le ha hab θ)
    (ellipseCurvature_pos ha hab θ).le (le_trans (abs_nonneg r) hr)

section VectorFlux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def ellipseTubeFlux (A₀ A₁ : FieldSpace → E) (a b r z : ℝ) : E :=
  ∫ θ in -(Real.pi / 2)..3 * Real.pi / 2,
    (ellipseTubeFactor a b θ r * (-a * Real.sin θ)) • A₀ (ellipseTubePoint a b θ r z) +
      (ellipseTubeFactor a b θ r * (b * Real.cos θ)) • A₁ (ellipseTubePoint a b θ r z)

theorem ellipseTubeFlux_sub_bound (A₀ A₁ : FieldSpace → E)
    (hA₀ : Continuous A₀) (hA₁ : Continuous A₁)
    {a b r z M D ε : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hM₀ : ∀ x, ‖A₀ x‖ ≤ M) (hM₁ : ∀ x, ‖A₁ x‖ ≤ M)
    (hD₀ : ∀ θ, ‖A₀ (ellipseTubePoint a b θ r z) - A₀ (ellipse a b θ)‖ ≤ D)
    (hD₁ : ∀ θ, ‖A₁ (ellipseTubePoint a b θ r z) - A₁ (ellipse a b θ)‖ ≤ D)
    (hε : ∀ θ, |ellipseTubeFactor a b θ r - 1| ≤ ε) :
    ‖ellipseTubeFlux A₀ A₁ a b r z - ellipseFlux A₀ A₁ a b‖ ≤
      (a + b) * (ε * M + D) * (2 * Real.pi) := by
  have hb : 0 ≤ b := ha.le.trans hab
  have hM : 0 ≤ M := (norm_nonneg (A₀ 0)).trans (hM₀ 0)
  have hε₀ : 0 ≤ ε := (abs_nonneg _).trans (hε 0)
  have hD : 0 ≤ D := (norm_nonneg _).trans (hD₀ 0)
  have hfactor : Continuous (fun θ => ellipseTubeFactor a b θ r) := by
    unfold ellipseTubeFactor ellipseCurvature
    exact continuous_const.sub (continuous_const.mul (continuous_const.div
      ((ellipseVelocity_continuous a b).norm.pow 3)
      (fun θ => pow_ne_zero 3 (ellipseVelocity_norm_pos ha hab θ).ne')))
  have hpoint : Continuous (fun θ => ellipseTubePoint a b θ r z) :=
    continuous_iff_continuousAt.mpr fun θ =>
      (ellipseTubePoint_hasDerivAt_angle ha hab θ r z).continuousAt
  have htube : Continuous (fun θ =>
      (ellipseTubeFactor a b θ r * (-a * Real.sin θ)) • A₀ (ellipseTubePoint a b θ r z) +
      (ellipseTubeFactor a b θ r * (b * Real.cos θ)) • A₁ (ellipseTubePoint a b θ r z)) :=
    ((hfactor.mul (continuous_const.mul Real.continuous_sin)).smul (hA₀.comp hpoint)).add
      ((hfactor.mul (continuous_const.mul Real.continuous_cos)).smul (hA₁.comp hpoint))
  have hcentral : Continuous (fun θ => (-a * Real.sin θ) • A₀ (ellipse a b θ) +
      (b * Real.cos θ) • A₁ (ellipse a b θ)) :=
    ((continuous_const.mul Real.continuous_sin).smul (hA₀.comp (ellipse_continuous a b))).add
      ((continuous_const.mul Real.continuous_cos).smul (hA₁.comp (ellipse_continuous a b)))
  unfold ellipseTubeFlux ellipseFlux
  rw [← intervalIntegral.integral_sub (htube.intervalIntegrable _ _)
    (hcentral.intervalIntegrable _ _)]
  have hp (θ : ℝ) :
      ‖(ellipseTubeFactor a b θ r * (-a * Real.sin θ)) • A₀ (ellipseTubePoint a b θ r z) +
        (ellipseTubeFactor a b θ r * (b * Real.cos θ)) • A₁ (ellipseTubePoint a b θ r z) -
        ((-a * Real.sin θ) • A₀ (ellipse a b θ) + (b * Real.cos θ) • A₁ (ellipse a b θ))‖ ≤
        (a + b) * (ε * M + D) := by
    have heq (A : FieldSpace → E) (c : ℝ) :
        (ellipseTubeFactor a b θ r * c) • A (ellipseTubePoint a b θ r z) - c • A (ellipse a b θ) =
          c • ((ellipseTubeFactor a b θ r - 1) • A (ellipseTubePoint a b θ r z) +
            (A (ellipseTubePoint a b θ r z) - A (ellipse a b θ))) := by module
    have hterm (A : FieldSpace → E) (hAM : ∀ x, ‖A x‖ ≤ M)
        (hAD : ‖A (ellipseTubePoint a b θ r z) - A (ellipse a b θ)‖ ≤ D)
        {c C : ℝ} (hc : |c| ≤ C) :
        ‖(ellipseTubeFactor a b θ r * c) • A (ellipseTubePoint a b θ r z) - c • A (ellipse a b θ)‖ ≤
          C * (ε * M + D) := by
      rw [heq, norm_smul, Real.norm_eq_abs]
      apply mul_le_mul hc _ (norm_nonneg _) ((abs_nonneg c).trans hc)
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul (hε θ) (hAM _) (norm_nonneg _) hε₀) hAD
    have hsin : |-a * Real.sin θ| ≤ a := by
      rw [abs_mul, abs_neg, abs_of_pos ha]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) ha.le).trans_eq (mul_one _)
    have hcos : |b * Real.cos θ| ≤ b := by
      rw [abs_mul, abs_of_nonneg hb]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) hb).trans_eq (mul_one _)
    rw [add_sub_add_comm]
    exact (norm_add_le _ _).trans ((add_le_add
      (hterm A₀ hM₀ (hD₀ θ) hsin) (hterm A₁ hM₁ (hD₁ θ) hcos)).trans_eq (by ring))
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(Real.pi / 2)) (b := 3 * Real.pi / 2) (fun θ _ => hp θ)
  have hlen : |3 * Real.pi / 2 - -(Real.pi / 2)| = 2 * Real.pi := by
    rw [show 3 * Real.pi / 2 - -(Real.pi / 2) = 2 * Real.pi by ring, abs_of_pos (by positivity)]
  simpa only [hlen] using hi

end VectorFlux

def tubeFieldFlux (F : Frame) (χ : ArticleCutoff) (infrared : Bool) (a b r z : ℝ) :
    Lp ℂ 2 photonMeasure :=
  ellipseTubeFlux (weightedFieldKernel F χ infrared 0)
    (weightedFieldKernel F χ infrared 1) a b r z

theorem tubeFieldFlux_sub_bound (F : Frame) (χ : ArticleCutoff) (infrared : Bool)
    {a b r z R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : |r| ≤ R) (hz : |z| ≤ R) :
    ‖tubeFieldFlux F χ infrared a b r z - centralFieldFlux F χ infrared a b‖ ≤
      (a + b) * ((R * (b / a ^ 2)) * cutoffMoment χ infrared +
        2 * cutoffModulus χ infrared (2 * R)) * (2 * Real.pi) := by
  have hdiff (i : Fin 3) (θ : ℝ) :
      ‖weightedFieldKernel F χ infrared i (ellipseTubePoint a b θ r z) -
        weightedFieldKernel F χ infrared i (ellipse a b θ)‖ ≤
        2 * cutoffModulus χ infrared (2 * R) := by
    apply (weightedFieldKernel_difference_le F χ infrared i _ _).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply cutoffModulus_mono χ infrared (norm_nonneg _)
    exact (ellipseTubePoint_distance ha hab θ r z).trans (by linarith)
  exact ellipseTubeFlux_sub_bound _ _ (weightedFieldKernel_continuous F χ infrared 0)
    (weightedFieldKernel_continuous F χ infrared 1) ha hab
    (weightedFieldKernel_norm_le F χ infrared 0) (weightedFieldKernel_norm_le F χ infrared 1)
    (hdiff 0) (hdiff 1) (fun θ => ellipseTubeFactor_error (θ := θ) ha hab hr)

/-- Cubic smallness holds uniformly on every loop in the thin tube. -/
theorem tubeFieldFlux_cubic_bound (F : Frame) (χ : ArticleCutoff) (infrared : Bool)
    {a b r z R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : |r| ≤ R) (hz : |z| ≤ R)
    (hRa : R ≤ a) (hε : R * (b / a ^ 2) ≤ b ^ 2) (hthin : a ≤ b ^ 3)
    (hd : cutoffModulus χ infrared (2 * a) ≤ b ^ 2) :
    ‖tubeFieldFlux F χ infrared a b r z‖ ≤
      (2 * Real.pi * (3 * cutoffMoment χ infrared + 5)) * b ^ 3 := by
  have hb : 0 ≤ b := ha.le.trans hab
  have hR : 0 ≤ R := (abs_nonneg r).trans hr
  have hM := cutoffMoment_nonneg χ infrared
  have hdR : cutoffModulus χ infrared (2 * R) ≤ b ^ 2 :=
    (cutoffModulus_mono χ infrared (by positivity) (by linarith)).trans hd
  have he : (R * (b / a ^ 2)) * cutoffMoment χ infrared +
      2 * cutoffModulus χ infrared (2 * R) ≤ b ^ 2 * (cutoffMoment χ infrared + 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hε hM]
  have he0 : 0 ≤ (R * (b / a ^ 2)) * cutoffMoment χ infrared +
      2 * cutoffModulus χ infrared (2 * R) := by
    have hd0 := cutoffModulus_nonneg χ infrared (2 * R)
    positivity
  have hdiff := (tubeFieldFlux_sub_bound F χ infrared ha hab hr hz).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul (show a + b ≤ 2 * b by linarith)
      he he0 (by positivity)) (show 0 ≤ 2 * Real.pi by positivity))
  have hcentral := centralFieldFlux_cubic_bound F χ infrared ha.le hb hthin hd
  calc
    ‖tubeFieldFlux F χ infrared a b r z‖ =
        ‖(tubeFieldFlux F χ infrared a b r z - centralFieldFlux F χ infrared a b) +
          centralFieldFlux F χ infrared a b‖ := by rw [sub_add_cancel]
    _ ≤ ‖tubeFieldFlux F χ infrared a b r z - centralFieldFlux F χ infrared a b‖ +
        ‖centralFieldFlux F χ infrared a b‖ := norm_add_le _ _
    _ ≤ (2 * b) * (b ^ 2 * (cutoffMoment χ infrared + 2)) * (2 * Real.pi) +
        (2 * Real.pi * (cutoffMoment χ infrared + 1)) * b ^ 3 := add_le_add hdiff hcentral
    _ = _ := by ring

theorem tubeFieldFlux_perimeter_bound (F : Frame) (χ : ArticleCutoff) (infrared : Bool)
    {a b r z R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : |r| ≤ R) (hz : |z| ≤ R)
    (hRa : R ≤ a) (hε : R * (b / a ^ 2) ≤ b ^ 2) (hthin : a ≤ b ^ 3)
    (hd : cutoffModulus χ infrared (2 * a) ≤ b ^ 2) :
    ‖tubeFieldFlux F χ infrared a b r z‖ ≤
      (2 * Real.pi * (3 * cutoffMoment χ infrared + 5)) * b * ellipsePerimeter a b ^ 2 := by
  refine (tubeFieldFlux_cubic_bound F χ infrared ha hab hr hz hRa hε hthin hd).trans ?_
  have hb : 0 ≤ b := ha.le.trans hab
  have hL : b ≤ ellipsePerimeter a b := by linarith [four_mul_le_ellipsePerimeter a b]
  have hM := cutoffMoment_nonneg χ infrared
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hb hL 2) hb)
    (show 0 ≤ 2 * Real.pi * (3 * cutoffMoment χ infrared + 5) by positivity)
  nlinarith

end GptLean.Nonattainment
