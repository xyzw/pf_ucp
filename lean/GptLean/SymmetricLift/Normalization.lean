import GptLean.SymmetricLift.SmoothPartition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FieldSimp

/-! Smooth radial normalization after a fixed continuous linear map. -/
noncomputable section
open scoped BigOperators ContDiff
namespace GptLean.SymmetricLift.Normalization

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The centered shape map when `P` is the centering projection. -/
def radial (P : E →L[ℝ] H) (x : E) : H := ‖P x‖⁻¹ • P x

/-- Actual derivative, with the scalar norm derivative written as a continuous linear map. -/
def radialDerivative (P : E →L[ℝ] H) (x : E) : E →L[ℝ] H :=
  ‖P x‖⁻¹ • P +
    (-((‖P x‖ ^ 2)⁻¹) • (fderiv ℝ (norm : H → ℝ) (P x)).comp P).smulRight (P x)

theorem radial_contDiffAt (P : E →L[ℝ] H) {x : E} (hx : P x ≠ 0) :
    ContDiffAt ℝ ∞ (radial P) x := by
  exact ((P.contDiff.contDiffAt.norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul
    P.contDiff.contDiffAt

theorem radial_contDiffOn (P : E →L[ℝ] H) :
    ContDiffOn ℝ ∞ (radial P) {x | P x ≠ 0} :=
  fun _ hx => (radial_contDiffAt P hx).contDiffWithinAt

theorem radial_hasFDerivAt (P : E →L[ℝ] H) {x : E} (hx : P x ≠ 0) :
    HasFDerivAt (radial P) (radialDerivative P x) x := by
  have hnorm : DifferentiableAt ℝ (norm : H → ℝ) (P x) :=
    (contDiffAt_norm (n := 1) ℝ hx).differentiableAt one_ne_zero
  exact ((hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x
    (hnorm.hasFDerivAt.comp x P.hasFDerivAt)).smul P.hasFDerivAt

theorem radial_fderiv (P : E →L[ℝ] H) {x : E} (hx : P x ≠ 0) :
    fderiv ℝ (radial P) x = radialDerivative P x :=
  (radial_hasFDerivAt P hx).fderiv

/-- The elementary factor two bound, independent of dimension and of `P`. -/
theorem radial_derivative_norm_le (P : E →L[ℝ] H) {x : E} (hx : P x ≠ 0) :
    ‖fderiv ℝ (radial P) x‖ ≤ 2 * ‖P‖ / ‖P x‖ := by
  have hn : 0 < ‖P x‖ := norm_pos_iff.mpr hx
  have hnD : ‖fderiv ℝ (norm : H → ℝ) (P x)‖ ≤ 1 :=
    NNReal.coe_one ▸ norm_fderiv_le_of_lipschitz ℝ
      (lipschitzWith_one_norm (E := H))
  have hcomp : ‖(fderiv ℝ (norm : H → ℝ) (P x)).comp P‖ ≤ ‖P‖ := by
    calc
      _ ≤ ‖fderiv ℝ (norm : H → ℝ) (P x)‖ * ‖P‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖P‖ := mul_le_mul_of_nonneg_right hnD (norm_nonneg P)
      _ = ‖P‖ := one_mul _
  rw [radial_fderiv P hx, radialDerivative]
  calc
    _ ≤ ‖‖P x‖⁻¹ • P‖ +
      ‖(-((‖P x‖ ^ 2)⁻¹) • (fderiv ℝ (norm : H → ℝ) (P x)).comp P).smulRight (P x)‖ :=
      norm_add_le _ _
    _ = ‖P x‖⁻¹ * ‖P‖ +
        (‖P x‖ ^ 2)⁻¹ * ‖(fderiv ℝ (norm : H → ℝ) (P x)).comp P‖ * ‖P x‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_smul]
      simp [Real.norm_of_nonneg, le_of_lt hn]
    _ ≤ ‖P x‖⁻¹ * ‖P‖ + (‖P x‖ ^ 2)⁻¹ * ‖P‖ * ‖P x‖ := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcomp (by positivity)) hn.le
    _ = 2 * ‖P‖ / ‖P x‖ := by
      field_simp [ne_of_gt hn]
      ring

theorem radial_norm (P : E →L[ℝ] H) {x : E} (hx : P x ≠ 0) :
    ‖radial P x‖ = 1 := by
  simp [radial, norm_smul, norm_ne_zero_iff.mpr hx]

/-- The derivative bound for the actual pulled-back atlas partition. -/
theorem partition_radial_bound {ι : Type*} [Fintype ι]
    (χ : ι → H → ℝ) (P : E →L[ℝ] H) {x : E} {A : ℝ}
    (hx : P x ≠ 0)
    (hχ : ∀ a, DifferentiableAt ℝ (χ a) (radial P x))
    (hA : (∑ a, ‖fderiv ℝ (χ a) (radial P x)‖ ^ 2) ≤ A) :
    (∑ a, ‖fderiv ℝ (χ a ∘ radial P) x‖ ^ 2) ≤
      (4 * A * ‖P‖ ^ 2) / ‖P x‖ ^ 2 := by
  have h := SmoothPartition.pullback_derivative_bound χ (radial P) hχ
    (radial_hasFDerivAt P hx).differentiableAt (radial_derivative_norm_le P hx) hA
  calc
    _ ≤ A * (2 * ‖P‖ / ‖P x‖) ^ 2 := h
    _ = _ := by ring

end GptLean.SymmetricLift.Normalization
