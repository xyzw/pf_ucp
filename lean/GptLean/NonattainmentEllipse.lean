import GptLean.Gaussian.FieldMoments
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
The central ellipse used in the nonattainment construction, with its actual
velocity, quantitative speed bounds, perimeter estimates and reflection law.
The parameter here is the ordinary angle. No tubular coordinate or arclength
realization is assumed by these estimates.
-/

noncomputable section

namespace GptLean.Nonattainment

open MeasureTheory Gaussian
open scoped InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 400000

def coordinateAxis (j : Fin 3) : FieldSpace := EuclideanSpace.single j 1

theorem coordinateAxis_norm (j : Fin 3) : ‖coordinateAxis j‖ = 1 := by
  simp [coordinateAxis]

def ellipse (a b t : ℝ) : FieldSpace :=
  (a * Real.cos t) • coordinateAxis 0 + (b * Real.sin t) • coordinateAxis 1

def ellipseVelocity (a b t : ℝ) : FieldSpace :=
  (-a * Real.sin t) • coordinateAxis 0 + (b * Real.cos t) • coordinateAxis 1

theorem ellipse_hasDerivAt (a b t : ℝ) :
    HasDerivAt (ellipse a b) (ellipseVelocity a b t) t := by
  unfold ellipse ellipseVelocity
  simpa only [mul_neg, neg_mul] using
    (((Real.hasDerivAt_cos t).const_mul a).smul_const (coordinateAxis 0)).fun_add
      (((Real.hasDerivAt_sin t).const_mul b).smul_const (coordinateAxis 1))

theorem ellipse_continuous (a b : ℝ) : Continuous (ellipse a b) := by
  unfold ellipse
  fun_prop

theorem ellipseVelocity_continuous (a b : ℝ) : Continuous (ellipseVelocity a b) := by
  unfold ellipseVelocity
  fun_prop

theorem ellipseVelocity_norm_sq (a b t : ℝ) :
    ‖ellipseVelocity a b t‖ ^ 2 =
      a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2 := by
  simp [ellipseVelocity, coordinateAxis, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_three, mul_pow]

theorem ellipseVelocity_norm_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (t : ℝ) :
    ‖ellipseVelocity a b t‖ ≤ b := by
  apply (sq_le_sq₀ (norm_nonneg _) (ha.trans hab)).mp
  rw [ellipseVelocity_norm_sq]
  calc
    a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2 ≤
        b ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2)
        (sq_nonneg (Real.sin t))]
    _ = b ^ 2 := by rw [← mul_add, Real.sin_sq_add_cos_sq, mul_one]

theorem le_ellipseVelocity_norm {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (t : ℝ) :
    a ≤ ‖ellipseVelocity a b t‖ := by
  apply (sq_le_sq₀ ha (norm_nonneg _)).mp
  rw [ellipseVelocity_norm_sq]
  calc
    a ^ 2 = a ^ 2 * Real.sin t ^ 2 + a ^ 2 * Real.cos t ^ 2 := by
      rw [← mul_add, Real.sin_sq_add_cos_sq, mul_one]
    a ^ 2 * Real.sin t ^ 2 + a ^ 2 * Real.cos t ^ 2 ≤
        a ^ 2 * Real.sin t ^ 2 + b ^ 2 * Real.cos t ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2)
        (sq_nonneg (Real.cos t))]

theorem ellipseVelocity_norm_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    0 < ‖ellipseVelocity a b t‖ := ha.trans_le (le_ellipseVelocity_norm ha.le hab t)

theorem ellipseVelocity_second_le (a b t : ℝ) :
    |b * Real.cos t| ≤ ‖ellipseVelocity a b t‖ := by
  have h := PiLp.norm_apply_le (ellipseVelocity a b t) (1 : Fin 3)
  simpa [ellipseVelocity, coordinateAxis, Real.norm_eq_abs] using h

def ellipsePerimeter (a b : ℝ) : ℝ :=
  ∫ t in -(Real.pi / 2)..3 * Real.pi / 2, ‖ellipseVelocity a b t‖

theorem ellipsePerimeter_nonneg (a b : ℝ) : 0 ≤ ellipsePerimeter a b :=
  intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun _ _ => norm_nonneg _)

theorem ellipsePerimeter_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ellipsePerimeter a b ≤ 2 * Real.pi * b := by
  have h := intervalIntegral.integral_mono (μ := volume)
    (f := fun t => ‖ellipseVelocity a b t‖) (g := fun _ => b)
    (by linarith [Real.pi_pos] :
      -(Real.pi / 2) ≤ 3 * Real.pi / 2)
    (ellipseVelocity_continuous a b |>.norm.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _) (fun t => ellipseVelocity_norm_le ha hab t)
  calc
    ellipsePerimeter a b ≤ ∫ _ in -(Real.pi / 2)..3 * Real.pi / 2, b := h
    _ = 2 * Real.pi * b := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring

theorem four_mul_le_ellipsePerimeter (a b : ℝ) :
    4 * b ≤ ellipsePerimeter a b := by
  have hleft := intervalIntegral.integral_mono (μ := volume)
    (f := fun t => b * Real.cos t) (g := fun t => ‖ellipseVelocity a b t‖)
    (by linarith [Real.pi_pos] :
      -(Real.pi / 2) ≤ Real.pi / 2)
    ((continuous_const.mul Real.continuous_cos).intervalIntegrable _ _)
    (ellipseVelocity_continuous a b |>.norm.intervalIntegrable _ _)
    (fun t => (le_abs_self (b * Real.cos t)).trans (ellipseVelocity_second_le a b t))
  have hright := intervalIntegral.integral_mono (μ := volume)
    (f := fun t => -b * Real.cos t) (g := fun t => ‖ellipseVelocity a b t‖)
    (by linarith [Real.pi_pos] :
      Real.pi / 2 ≤ 3 * Real.pi / 2)
    ((continuous_const.mul Real.continuous_cos).intervalIntegrable _ _)
    (ellipseVelocity_continuous a b |>.norm.intervalIntegrable _ _)
    (fun t => by
      simpa only [neg_mul] using (neg_le_abs (b * Real.cos t)).trans
        (ellipseVelocity_second_le a b t))
  have hs : Real.sin (3 * Real.pi / 2) = -1 := by
    have he : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
    rw [he, Real.sin_add_pi, Real.sin_pi_div_two]
  have hl : 2 * b ≤ ∫ t in -(Real.pi / 2)..Real.pi / 2,
      ‖ellipseVelocity a b t‖ := by
    rw [intervalIntegral.integral_const_mul, integral_cos,
      Real.sin_neg, Real.sin_pi_div_two] at hleft
    linarith
  have hr : 2 * b ≤ ∫ t in Real.pi / 2..3 * Real.pi / 2,
      ‖ellipseVelocity a b t‖ := by
    have hright' : (∫ t in Real.pi / 2..3 * Real.pi / 2, -b * Real.cos t) ≤
        ∫ t in Real.pi / 2..3 * Real.pi / 2, ‖ellipseVelocity a b t‖ := by
      simpa only [neg_mul] using hright
    rw [intervalIntegral.integral_const_mul, integral_cos, hs,
      Real.sin_pi_div_two] at hright'
    linarith
  unfold ellipsePerimeter
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.pi / 2)
    (ellipseVelocity_continuous a b |>.norm.intervalIntegrable _ _)
    (ellipseVelocity_continuous a b |>.norm.intervalIntegrable _ _)]
  linarith

theorem ellipse_reflected (a b t : ℝ) :
    ellipse a b (Real.pi - t) =
      (-a * Real.cos t) • coordinateAxis 0 + (b * Real.sin t) • coordinateAxis 1 := by
  simp [ellipse, Real.cos_pi_sub, Real.sin_pi_sub, mul_neg, neg_mul]

theorem ellipse_reflection_distance {a : ℝ} (ha : 0 ≤ a) (b t : ℝ) :
    ‖ellipse a b t - ellipse a b (Real.pi - t)‖ ≤ 2 * a := by
  have he : ellipse a b t - ellipse a b (Real.pi - t) =
      (2 * a * Real.cos t) • coordinateAxis 0 := by
    rw [ellipse_reflected]
    unfold ellipse
    module
  rw [he, norm_smul, coordinateAxis_norm, mul_one, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 * a)]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) (by positivity)).trans_eq
    (mul_one _)

end GptLean.Nonattainment
