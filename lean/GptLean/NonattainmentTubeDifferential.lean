import GptLean.NonattainmentTubeGeometry
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Differential formulas and the positive volume factor of the explicit ellipse
normal chart. All curvature bounds are derived from the ellipse parameters.
-/

noncomputable section

namespace GptLean.Nonattainment

open Gaussian
open scoped InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 600000

def ellipseCurvature (a b θ : ℝ) : ℝ := a * b / ‖ellipseVelocity a b θ‖ ^ 3

theorem ellipseVelocity_hasDerivAt (a b θ : ℝ) :
    HasDerivAt (ellipseVelocity a b) (-ellipse a b θ) θ := by
  unfold ellipseVelocity ellipse
  convert! (((Real.hasDerivAt_sin θ).const_mul (-a)).smul_const (coordinateAxis 0)).fun_add
    (((Real.hasDerivAt_cos θ).const_mul b).smul_const (coordinateAxis 1)) using 1
  module

theorem ellipseSpeed_hasDerivAt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    HasDerivAt (fun t => ‖ellipseVelocity a b t‖)
      (((a ^ 2 - b ^ 2) * Real.sin θ * Real.cos θ) / ‖ellipseVelocity a b θ‖) θ := by
  have hp := ellipseVelocity_norm_pos ha hab θ
  have h := (ellipseVelocity_hasDerivAt a b θ).norm_sq.sqrt (pow_ne_zero 2 hp.ne')
  have hi : ⟪ellipseVelocity a b θ, -ellipse a b θ⟫_ℝ =
      (a ^ 2 - b ^ 2) * Real.sin θ * Real.cos θ := by
    simp [ellipseVelocity, ellipse, coordinateAxis, PiLp.inner_apply, Fin.sum_univ_three]
    ring
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, hi, mul_div_mul_left _ _ (show (2 : ℝ) ≠ 0 by norm_num)] using h

theorem ellipseNormalNumerator_hasDerivAt (a b θ : ℝ) :
    HasDerivAt (ellipseNormalNumerator a b)
      ((-b * Real.sin θ) • coordinateAxis 0 + (a * Real.cos θ) • coordinateAxis 1) θ := by
  unfold ellipseNormalNumerator
  simpa only [mul_neg, neg_mul] using
    (((Real.hasDerivAt_cos θ).const_mul b).smul_const (coordinateAxis 0)).fun_add
      (((Real.hasDerivAt_sin θ).const_mul a).smul_const (coordinateAxis 1))

theorem ellipseNormal_hasDerivAt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    HasDerivAt (ellipseNormal a b)
      (-ellipseCurvature a b θ • ellipseVelocity a b θ) θ := by
  have hp := ellipseVelocity_norm_pos ha hab θ
  have h := ((ellipseSpeed_hasDerivAt ha hab θ).inv hp.ne').fun_smul
    (ellipseNormalNumerator_hasDerivAt a b θ)
  have hsq : ‖-((a * Real.sin θ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) +
      (b * Real.cos θ) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)‖ ^ 2 =
      a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2 := by
    simpa [ellipseVelocity, coordinateAxis] using ellipseVelocity_norm_sq a b θ
  unfold ellipseNormal
  convert! h.fun_neg using 1
  ext i
  fin_cases i <;>
    simp [ellipseCurvature, ellipseVelocity, ellipseNormalNumerator, coordinateAxis]
  · field_simp
    rw [hsq]
    have hi : Real.cos θ ^ 2 * (a ^ 2 - b ^ 2) +
        (a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2) = a ^ 2 := by
      nlinarith [congrArg (fun r : ℝ => a ^ 2 * r) (Real.sin_sq_add_cos_sq θ)]
    rw [hi]
    ring
  · field_simp
    rw [hsq]
    have hi : Real.sin θ ^ 2 * (a ^ 2 - b ^ 2) +
        -(a ^ 2 * Real.sin θ ^ 2 + b ^ 2 * Real.cos θ ^ 2) = -(b ^ 2) := by
      nlinarith [congrArg (fun r : ℝ => b ^ 2 * r) (Real.sin_sq_add_cos_sq θ)]
    rw [hi]
    ring

theorem ellipseCurvature_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    0 < ellipseCurvature a b θ := by
  unfold ellipseCurvature
  exact div_pos (mul_pos ha (ha.trans_le hab)) (pow_pos (ellipseVelocity_norm_pos ha hab θ) 3)

theorem ellipseCurvature_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (θ : ℝ) :
    ellipseCurvature a b θ ≤ b / a ^ 2 := by
  have hp := ellipseVelocity_norm_pos ha hab θ
  have hcube : a ^ 3 ≤ ‖ellipseVelocity a b θ‖ ^ 3 :=
    pow_le_pow_left₀ ha.le (le_ellipseVelocity_norm ha.le hab θ) 3
  calc
    ellipseCurvature a b θ ≤ a * b / a ^ 3 :=
      div_le_div_of_nonneg_left (mul_nonneg ha.le (ha.trans_le hab).le) (pow_pos ha 3) hcube
    _ = b / a ^ 2 := by field_simp

def ellipseTubePoint (a b θ r z : ℝ) : FieldSpace :=
  ellipse a b θ + r • ellipseNormal a b θ + z • coordinateAxis 2

def ellipseTubeFactor (a b θ r : ℝ) : ℝ := 1 - r * ellipseCurvature a b θ

theorem ellipseTubePoint_hasDerivAt_angle {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (θ r z : ℝ) :
    HasDerivAt (fun t => ellipseTubePoint a b t r z)
      (ellipseTubeFactor a b θ r • ellipseVelocity a b θ) θ := by
  have h := ((ellipse_hasDerivAt a b θ).fun_add
    ((ellipseNormal_hasDerivAt ha hab θ).const_smul r)).add_const (z • coordinateAxis 2)
  convert! h using 1
  simp only [ellipseTubeFactor]
  module

theorem ellipseTubeFactor_bounds {a b θ r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : |r| < a ^ 2 / (2 * b)) :
    1 / 2 < ellipseTubeFactor a b θ r ∧ ellipseTubeFactor a b θ r < 3 / 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hk := ellipseCurvature_pos ha hab θ
  have hkb := ellipseCurvature_le ha hab θ
  have habs : |r * ellipseCurvature a b θ| < 1 / 2 := by
    rw [abs_mul, abs_of_pos hk]
    calc
      |r| * ellipseCurvature a b θ ≤ |r| * (b / a ^ 2) :=
        mul_le_mul_of_nonneg_left hkb (abs_nonneg _)
      _ < (a ^ 2 / (2 * b)) * (b / a ^ 2) :=
        mul_lt_mul_of_pos_right hr (by positivity)
      _ = 1 / 2 := by field_simp
  rw [abs_lt] at habs
  dsimp [ellipseTubeFactor]
  constructor <;> linarith

/-- The oriented volume factor of angle, inward-normal, and vertical columns. -/
def ellipseTubeJacobian (a b θ r : ℝ) : ℝ :=
  ‖ellipseVelocity a b θ‖ * ellipseTubeFactor a b θ r

theorem ellipseTubeJacobian_pos {a b θ r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : |r| < a ^ 2 / (2 * b)) : 0 < ellipseTubeJacobian a b θ r := by
  apply mul_pos (ellipseVelocity_norm_pos ha hab θ)
  have h := (ellipseTubeFactor_bounds (θ := θ) ha hab hr).1
  linarith

end GptLean.Nonattainment
