import PfHk.SpinfulCounterexampleField
import GptLean.ElectronicH1Multiplier

/-! Bounded smooth field coordinates and their derivatives. -/

noncomputable section
namespace PfHk.SpinfulCounterexampleField

open scoped InnerProductSpace ContDiff

set_option Elab.async false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false

theorem field_component_abs_le (j : Fin 3) (x : Space) : |field x j| ≤ 1 / 2 :=
  (PiLp.norm_apply_le (field x) j).trans (field_norm_le_half x)

theorem weight_rotation_abs_le (j : Fin 3) (x : Space) :
    |weight x * rotation x j| ≤ 1 / 2 := by
  simpa only [field_eq_weight_rotation, PiLp.smul_apply, smul_eq_mul] using
    field_component_abs_le j x

theorem weight_projection_abs_le (j : Fin 3) (x : Space) :
    |weight x * projection x j| ≤ 1 / 2 := by
  fin_cases j
  · simpa using weight_rotation_abs_le 1 x
  · change |weight x * x 1| ≤ 1 / 2
    simpa only [CounterexampleField.rotation_coord_zero, mul_neg,
      abs_neg] using weight_rotation_abs_le 0 x
  · simp

theorem rotation_projection_single_abs_le (i j : Fin 3) :
    |rotation (projection (EuclideanSpace.single i 1)) j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [projection, projectionLinear, CounterexampleField.rotation,
      CounterexampleField.rotationLinear, PiLp.single_apply]

theorem field_coordinate_derivative (i j : Fin 3) (x : Space) :
    fderiv ℝ (fun y => field y j) x (EuclideanSpace.single i 1) =
      weight x * rotation (projection (EuclideanSpace.single i 1)) j -
        2 * (weight x * projection x i) * (weight x * rotation x j) := by
  have hd := ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x
    (hasFDerivAt_field x)).fderiv
  change fderiv ℝ (fun y => field y j) x = _ at hd
  rw [hd]
  fin_cases i <;> fin_cases j
  all_goals
    simp [weight, ContinuousLinearMap.smulRight_apply, PiLp.inner_apply,
      projection, projectionLinear, CounterexampleField.rotation,
      CounterexampleField.rotationLinear, Fin.sum_univ_succ]
    <;> ring

theorem field_coordinate_derivative_bound (i j : Fin 3) (x : Space) :
    |fderiv ℝ (fun y => field y j) x (EuclideanSpace.single i 1)| ≤ 2 := by
  rw [field_coordinate_derivative]
  calc
    _ ≤ |weight x * rotation (projection (EuclideanSpace.single i 1)) j| +
        |2 * (weight x * projection x i) * (weight x * rotation x j)| := abs_sub _ _
    _ = weight x * |rotation (projection (EuclideanSpace.single i 1)) j| +
        2 * |weight x * projection x i| * |weight x * rotation x j| := by
      simp only [abs_mul, abs_of_pos (weight_pos x), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 1 * 1 + 2 * (1 / 2) * (1 / 2) := by
      gcongr
      · exact weight_le_one x
      · exact rotation_projection_single_abs_le i j
      · exact weight_projection_abs_le i x
      · exact weight_rotation_abs_le j x
    _ ≤ 2 := by norm_num

def fieldSmoothMultiplier (j : Fin 3) : GptLean.ElectronicH1Multiplier.SmoothMultiplier (Fin 3) where
  weight := fun x => field x j
  smooth := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp contDiff_field
  bound := 1 / 2
  bounded := field_component_abs_le j
  derivativeBound := 2
  derivative_bounded := fun i x => field_coordinate_derivative_bound i j x

theorem field_coordinate_derivative_two (j : Fin 3) (x : Space) :
    fderiv ℝ (fun y => field y j) x (EuclideanSpace.single 2 1) = 0 := by
  rw [field_coordinate_derivative]
  fin_cases j <;>
    simp [projection, projectionLinear, CounterexampleField.rotation, CounterexampleField.rotationLinear]

theorem field_planar_curl (x : Space) :
    fderiv ℝ (fun y => field y 1) x (EuclideanSpace.single 0 1) -
      fderiv ℝ (fun y => field y 0) x (EuclideanSpace.single 1 1) =
      2 * weight x ^ 2 := by
  have hc := congrArg (fun y : Space => y 2) (curl_field x)
  have hd (i j : Fin 3) : fderiv ℝ (fun y => field y j) x (EuclideanSpace.single i 1) =
      fderiv ℝ field x (EuclideanSpace.single i 1) j :=
    congrArg (fun L : Space →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
      (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x
        (differentiable_field x).hasFDerivAt).fderiv)
  simpa [curl, CounterexampleField.curl, hd] using hc

end PfHk.SpinfulCounterexampleField
