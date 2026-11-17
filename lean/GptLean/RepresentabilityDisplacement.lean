import GptLean.RepresentabilityKernel
import GptLean.RepresentabilityFieldEquation

/-!
The field equation on the actual density-weighted L2 space. The integral
kernel is constructed from the bounded coupling family. Coercivity of the
finite-dimensional diagonal Gram map is lifted by integration, and the
solution satisfies both the pointwise integral equation and its norm bound.
-/

noncomputable section

namespace GptLean.Representability

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {X V H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsFiniteMeasure μ]

omit [CompleteSpace V] [IsFiniteMeasure μ] in
/-- Coercivity of a constant Gram matrix passes to any weighted L2 space. -/
theorem gram_compLp_coercive (M : V →L[ℝ] V) (ell : ℝ)
    (hM : ∀ v, ell * ‖v‖ ^ 2 ≤ ⟪v, M v⟫_ℝ) (u : Lp V 2 μ) :
    ell * ‖u‖ ^ 2 ≤ ⟪u, M.compLpL 2 μ u⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def,
    ← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner u u).const_mul ell)
    (L2.integrable_inner u (M.compLpL 2 μ u))
  filter_upwards [M.coeFn_compLpL u] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
  exact hM (u x)

namespace BoundedCoupling

variable (G : BoundedCoupling μ V H)

/-- Existence and uniqueness for the constructed kernel on weighted L2.
Only the coercivity of the ordinary diagonal Gram map remains an input. -/
theorem displacement_exists (M : V →L[ℝ] V)
    (N : ℕ) (hN : 1 ≤ N) (ell : ℝ) (hell : 0 < ell)
    (hM : ∀ v, ell * ‖v‖ ^ 2 ≤ ⟪v, M v⟫_ℝ) (a : Lp V 2 μ) :
    ∃ u : Lp V 2 μ,
      M.compLpL 2 μ u + (((N : ℝ) - 1) / (N : ℝ)) • G.kernel u = a ∧
      ‖u‖ ≤ ell⁻¹ * ‖a‖ ∧
      ∀ v, M.compLpL 2 μ v + (((N : ℝ) - 1) / (N : ℝ)) • G.kernel v = a →
        v = u :=
  photonic_field_equation (M.compLpL 2 μ) G.kernel N hN ell hell
    (gram_compLp_coercive M ell hM) G.kernel_nonneg a

/-- The unique L2 displacement solves the article's Bochner integral
equation almost everywhere, including on densities with zeros. -/
theorem displacement_integral_exists (M : V →L[ℝ] V)
    (N : ℕ) (hN : 1 ≤ N) (ell : ℝ) (hell : 0 < ell)
    (hM : ∀ v, ell * ‖v‖ ^ 2 ≤ ⟪v, M v⟫_ℝ) (a : Lp V 2 μ) :
    ∃ u : Lp V 2 μ, ‖u‖ ≤ ell⁻¹ * ‖a‖ ∧
      ∀ᵐ x ∂μ, M (u x) + (((N : ℝ) - 1) / (N : ℝ)) •
        (∫ y, (2 : ℝ) • ((G.value x).adjoint (G.value y (u y))) ∂μ) = a x := by
  obtain ⟨u, heq, hbound, _⟩ := G.displacement_exists M N hN ell hell hM a
  refine ⟨u, hbound, ?_⟩
  have hpoint : (M.compLpL 2 μ u + (((N : ℝ) - 1) / (N : ℝ)) • G.kernel u : Lp V 2 μ)
      =ᵐ[μ] (a : X → V) := by rw [heq]
  filter_upwards [hpoint,
    Lp.coeFn_add (M.compLpL 2 μ u) ((((N : ℝ) - 1) / (N : ℝ)) • G.kernel u),
    Lp.coeFn_smul (((N : ℝ) - 1) / (N : ℝ)) (G.kernel u),
    M.coeFn_compLpL u, G.kernel_integral_ae u] with x hx hadd hsmul hM hk
  simpa only [hadd, Pi.add_apply, hsmul, Pi.smul_apply, hM, hk] using hx

end BoundedCoupling

end GptLean.Representability
