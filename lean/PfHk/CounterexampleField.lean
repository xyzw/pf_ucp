import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
The explicit bounded vector field in `prop-zero-coupling-counterexample`.
This file proves its bound, zero divergence, tangency to spheres, distinct
curls at the origin, and the shifted-scalar cancellation. It does not assert
the hydrogenic spectral or ground-state claims of that proposition.
-/

noncomputable section

namespace PfHk.CounterexampleField

open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

abbrev Space := EuclideanSpace ℝ (Fin 3)

def rotationLinear : Space →ₗ[ℝ] Space where
  toFun x := WithLp.toLp 2 ![-x 1, x 0, 0]
  map_add' x y := by
    apply PiLp.ext
    intro a
    fin_cases a <;> simp [add_comm]
  map_smul' t x := by
    apply PiLp.ext
    intro a
    fin_cases a <;> simp

def rotation : Space →L[ℝ] Space := rotationLinear.toContinuousLinearMap

@[simp] theorem rotation_coord_zero (x : Space) : rotation x 0 = -x 1 := rfl
@[simp] theorem rotation_coord_one (x : Space) : rotation x 1 = x 0 := rfl
@[simp] theorem rotation_coord_two (x : Space) : rotation x 2 = 0 := rfl

def denominator (x : Space) : ℝ := 1 + ‖x‖ ^ 2

theorem denominator_pos (x : Space) : 0 < denominator x := by
  unfold denominator
  positivity

/-- The paper's field `(-x₂,x₁,0)/(1+|x|²)`. -/
def field (x : Space) : Space := (denominator x)⁻¹ • rotation x

theorem field_components (x : Space) :
    field x 0 = -x 1 / (1 + ‖x‖ ^ 2) ∧
    field x 1 = x 0 / (1 + ‖x‖ ^ 2) ∧ field x 2 = 0 := by
  simp [field, denominator, div_eq_mul_inv, mul_comm]

theorem norm_rotation_le (x : Space) : ‖rotation x‖ ≤ ‖x‖ := by
  have hsq : ‖rotation x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_succ]
    nlinarith [sq_nonneg (x 2)]
  nlinarith [norm_nonneg (rotation x), norm_nonneg x]

theorem field_norm_le_radial (x : Space) :
    ‖field x‖ ≤ ‖x‖ / (1 + ‖x‖ ^ 2) := by
  rw [field, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (denominator_pos x).le)]
  exact (mul_le_mul_of_nonneg_left (norm_rotation_le x)
    (inv_nonneg.mpr (denominator_pos x).le)).trans_eq (by
      simp [denominator, div_eq_mul_inv, mul_comm])

/-- The global bound used to place every external vector potential in L∞. -/
theorem field_norm_le_half (x : Space) : ‖field x‖ ≤ 1 / 2 := by
  apply (field_norm_le_radial x).trans
  apply (div_le_iff₀ (denominator_pos x)).2
  unfold denominator
  nlinarith [sq_nonneg (‖x‖ - 1)]

theorem field_tangent (x : Space) : inner ℝ (field x) x = 0 := by
  rw [field, real_inner_smul_left]
  have h : inner ℝ (rotation x) x = 0 := by
    simp [PiLp.inner_apply, Fin.sum_univ_succ]
    ring
  rw [h, mul_zero]

theorem hasFDerivAt_denominator (x : Space) :
    HasFDerivAt denominator (2 • innerSL ℝ x) x := by
  change HasFDerivAt (fun y : Space => (1 : ℝ) + ‖y‖ ^ 2) (2 • innerSL ℝ x) x
  exact (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1

theorem hasFDerivAt_field (x : Space) :
    HasFDerivAt field
      ((denominator x)⁻¹ • rotation +
        ((-(denominator x ^ 2)⁻¹) • (2 • innerSL ℝ x)).smulRight (rotation x)) x := by
  exact ((hasDerivAt_inv (denominator_pos x).ne').comp_hasFDerivAt x
    (hasFDerivAt_denominator x)).smul rotation.hasFDerivAt

theorem differentiable_field : Differentiable ℝ field :=
  fun x => (hasFDerivAt_field x).differentiableAt

/-- The field belongs to the stated bounded-potential class. -/
theorem field_memLp_top : MeasureTheory.MemLp field ⊤ MeasureTheory.volume :=
  MeasureTheory.memLp_top_of_bound differentiable_field.continuous.aestronglyMeasurable
    (1 / 2) (Filter.Eventually.of_forall field_norm_le_half)

/-- Pointwise divergence, defined as the trace of the Fréchet derivative. -/
def divergence (a : Space → Space) (x : Space) : ℝ :=
  ∑ μ : Fin 3, fderiv ℝ a x (EuclideanSpace.single μ 1) μ

theorem divergence_field (x : Space) : divergence field x = 0 := by
  unfold divergence
  rw [(hasFDerivAt_field x).fderiv]
  simp [Fin.sum_univ_succ, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.inner_single_right]
  ring

/-- The usual three-dimensional curl, expressed through the Fréchet derivative. -/
def curl (a : Space → Space) (x : Space) : Space :=
  WithLp.toLp 2
    ![fderiv ℝ a x (EuclideanSpace.single 1 1) 2 -
        fderiv ℝ a x (EuclideanSpace.single 2 1) 1,
      fderiv ℝ a x (EuclideanSpace.single 2 1) 0 -
        fderiv ℝ a x (EuclideanSpace.single 0 1) 2,
      fderiv ℝ a x (EuclideanSpace.single 0 1) 1 -
        fderiv ℝ a x (EuclideanSpace.single 1 1) 0]

theorem fderiv_field_zero : fderiv ℝ field 0 = rotation := by
  rw [(hasFDerivAt_field 0).fderiv]
  simp [denominator]

theorem curl_field_zero : curl field 0 = WithLp.toLp 2 ![0, 0, 2] := by
  apply PiLp.ext
  intro μ
  fin_cases μ <;> norm_num [curl, fderiv_field_zero]
  all_goals decide

def vectorPotential (t : ℝ) (x : Space) : Space := t • field x

theorem vectorPotential_norm_le (t : ℝ) (x : Space) :
    ‖vectorPotential t x‖ ≤ |t| / 2 := by
  rw [vectorPotential, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (field_norm_le_half x) (abs_nonneg t)).trans_eq (by ring)

theorem curl_vectorPotential_zero (t : ℝ) :
    curl (vectorPotential t) 0 = WithLp.toLp 2 ![0, 0, 2 * t] := by
  have hd : fderiv ℝ (vectorPotential t) 0 = t • rotation := by
    exact ((hasFDerivAt_field 0).const_smul t).fderiv.trans (by
      rw [← (hasFDerivAt_field 0).fderiv, fderiv_field_zero])
  apply PiLp.ext
  intro μ
  fin_cases μ <;> simp [curl, hd]
  ring

/-- Distinct members of the family have distinct magnetic fields. -/
theorem distinct_curls {s t : ℝ} (hst : s ≠ t) :
    curl (vectorPotential s) 0 ≠ curl (vectorPotential t) 0 := by
  intro h
  have hc := congrArg (fun v : Space => v 2) h
  rw [curl_vectorPotential_zero, curl_vectorPotential_zero] at hc
  apply hst
  change 2 * s = 2 * t at hc
  linarith

theorem distinct_magnetic_fields {s t : ℝ} (hst : s ≠ t) :
    curl (vectorPotential s) ≠ curl (vectorPotential t) := by
  intro h
  exact distinct_curls hst (congrFun h 0)

def scalarPotential (Z t : ℝ) (x : Space) : ℝ :=
  -Z / ‖x‖ - t ^ 2 / 2 * ‖field x‖ ^ 2

/-- All members have the same diamagnetically shifted scalar potential. -/
theorem shifted_scalar_cancel (Z t : ℝ) (x : Space) :
    scalarPotential Z t x + ‖vectorPotential t x‖ ^ 2 / 2 = -Z / ‖x‖ := by
  simp only [scalarPotential, vectorPotential, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

end PfHk.CounterexampleField
