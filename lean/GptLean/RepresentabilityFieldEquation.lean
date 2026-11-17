import GptLean.Representability
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
The Hilbert-space field equation in Step 3 of the photonic representability
proof. Boundedness is encoded by continuous linear maps. Coercivity supplies
existence and uniqueness through Lax–Milgram, and the estimate reuses the
previously verified displacement bound. Symmetry is not needed for this step.

The construction of the weighted kernel operator from the continuum coupling
functions is separate from this operator-theoretic result.
-/

noncomputable section

namespace GptLean.Representability

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The bilinear form associated with the bounded field operator. -/
def fieldBilinearForm (T : H →L[ℝ] H) : H →L[ℝ] H →L[ℝ] ℝ :=
  (innerSL ℝ).comp T

@[simp]
theorem fieldBilinearForm_apply (T : H →L[ℝ] H) (u v : H) :
    fieldBilinearForm T u v = ⟪T u, v⟫_ℝ := rfl

theorem fieldBilinearForm_isCoercive (T : H →L[ℝ] H)
    (ell : ℝ) (hell : 0 < ell)
    (hT : ∀ u, ell * ‖u‖ ^ 2 ≤ ⟪u, T u⟫_ℝ) :
    IsCoercive (fieldBilinearForm T) := by
  refine ⟨ell, hell, fun u => ?_⟩
  simpa only [fieldBilinearForm_apply, real_inner_comm (T u) u,
    pow_two, mul_assoc] using hT u

variable [CompleteSpace H]

/-- A bounded coercive real Hilbert-space operator has a bounded inverse. -/
def coerciveFieldEquiv (T : H →L[ℝ] H) (ell : ℝ) (hell : 0 < ell)
    (hT : ∀ u, ell * ‖u‖ ^ 2 ≤ ⟪u, T u⟫_ℝ) : H ≃L[ℝ] H :=
  (fieldBilinearForm_isCoercive T ell hell hT).continuousLinearEquivOfBilin

@[simp]
theorem coerciveFieldEquiv_apply (T : H →L[ℝ] H) (ell : ℝ) (hell : 0 < ell)
    (hT : ∀ u, ell * ‖u‖ ^ 2 ≤ ⟪u, T u⟫_ℝ) (u : H) :
    coerciveFieldEquiv T ell hell hT u = T u := by
  apply ext_inner_right ℝ
  intro v
  exact (fieldBilinearForm_isCoercive T ell hell hT).continuousLinearEquivOfBilin_apply u v

theorem coercive_operator_bijective (T : H →L[ℝ] H)
    (ell : ℝ) (hell : 0 < ell)
    (hT : ∀ u, ell * ‖u‖ ^ 2 ≤ ⟪u, T u⟫_ℝ) :
    Function.Bijective T := by
  have heq : ⇑(coerciveFieldEquiv T ell hell hT) = ⇑T :=
    funext (coerciveFieldEquiv_apply T ell hell hT)
  rw [← heq]
  exact (coerciveFieldEquiv T ell hell hT).bijective

/-- The unique displacement solving the prescribed field equation. -/
theorem coercive_field_equation (T : H →L[ℝ] H)
    (ell : ℝ) (hell : 0 < ell)
    (hT : ∀ u, ell * ‖u‖ ^ 2 ≤ ⟪u, T u⟫_ℝ) (a : H) :
    ∃! u, T u = a :=
  (coercive_operator_bijective T ell hell hT).existsUnique a

/-- Existence, uniqueness, and the quantitative estimate in
`photonic-field-equation`, with no assumed inverse or solution. -/
theorem coercive_field_equation_with_bound (T : H →L[ℝ] H)
    (ell : ℝ) (hell : 0 < ell)
    (hT : ∀ u, ell * ‖u‖ ^ 2 ≤ ⟪u, T u⟫_ℝ) (a : H) :
    ∃ u, T u = a ∧ ‖u‖ ≤ ell⁻¹ * ‖a‖ ∧ ∀ v, T v = a → v = u := by
  obtain ⟨u, hu, huniq⟩ := coercive_field_equation T ell hell hT a
  exact ⟨u, hu, displacement_solution_bound T ell hell hT u a hu, huniq⟩

/-- Application to the positive-kernel field operator `M + α K`.
The maps encode bounded operators on the real weighted Hilbert space. -/
theorem positive_kernel_field_equation (M K : H →L[ℝ] H)
    (ell α : ℝ) (hell : 0 < ell) (hα : 0 ≤ α)
    (hM : ∀ u, ell * ‖u‖ ^ 2 ≤ ⟪u, M u⟫_ℝ)
    (hK : ∀ u, 0 ≤ ⟪u, K u⟫_ℝ) (a : H) :
    ∃ u, M u + α • K u = a ∧ ‖u‖ ≤ ell⁻¹ * ‖a‖ ∧
      ∀ v, M v + α • K v = a → v = u := by
  exact coercive_field_equation_with_bound (M + α • K) ell hell
    (displacement_coercive M K ell α hM hK hα) a

/-- The coefficient `(N - 1) / N` of the photonic representability proof. -/
theorem photonic_field_equation (M K : H →L[ℝ] H)
    (N : ℕ) (hN : 1 ≤ N) (ell : ℝ) (hell : 0 < ell)
    (hM : ∀ u, ell * ‖u‖ ^ 2 ≤ ⟪u, M u⟫_ℝ)
    (hK : ∀ u, 0 ≤ ⟪u, K u⟫_ℝ) (a : H) :
    ∃ u, M u + (((N : ℝ) - 1) / (N : ℝ)) • K u = a ∧
      ‖u‖ ≤ ell⁻¹ * ‖a‖ ∧
      ∀ v, M v + (((N : ℝ) - 1) / (N : ℝ)) • K v = a → v = u :=
  positive_kernel_field_equation M K ell _ hell
    (particle_coefficient_nonnegative N hN) hM hK a

end GptLean.Representability
