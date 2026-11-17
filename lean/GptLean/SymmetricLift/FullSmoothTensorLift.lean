import GptLean.SymmetricLift.FullMetric

/-!
The complete smooth tensor-lift result, with one scalar sequence valid for
every one-particle Hilbert space. The witness is the explicit strong-recursive
construction. The only input is the standard tensor-space background.
Its canonical Hilbert tensor realization is not constructed in this file.
The quantitative formulation uses an arbitrary Lipschitz constant instead
of a separately formalized weak-gradient essential supremum.

This file packages the smooth isometry lemma. Sobolev removability across
collision diagonals is a separate analytic statement.
-/

noncomputable section

namespace GptLean.SymmetricLift

open TopologicalSpace
open scoped NNReal

section FixedSpace
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]

/-- All assertions of the smooth isometry lemma, as properties of a witness.
No field is an assumption used to construct the witness. -/
structure FullSmoothTensorLiftProperties (B : TensorBackground V) (n : ℕ)
    (L : LiftCandidate B n) (b : ℝ) : Prop where
  complete : CompleteSpace L.target
  separable : SeparableSpace L.target
  finiteDimensional : FiniteDimensional ℂ V → FiniteDimensional ℂ L.target
  qualitative : SmoothLiftProperties B n L
  quantitative : LiftMetricProperties B n L b

/-- Pair control applies to every unit map, including non-Lipschitz maps.
For Lipschitz maps the two estimates give the stated minimum. -/
theorem FullSmoothTensorLiftProperties.min_bound
    {B : TensorBackground V} {n : ℕ} {L : LiftCandidate B n} {b : ℝ}
    (h : FullSmoothTensorLiftProperties B n L b)
    {x : Configuration n} (hx : x ∈ distinctConfigurations n)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1)
    (C : ℝ≥0) (hC : LipschitzWith C t) :
    operatorCoordinateMetric L.operator x (configurationTensor B t x) ≤
      b * min (pairEnergy x) ((C : ℝ) ^ 2) := by
  rcases le_total (pairEnergy x) ((C : ℝ) ^ 2) with hp | hp
  · simpa only [min_eq_left hp] using h.quantitative.pair x hx t ht
  · simpa only [min_eq_right hp] using h.quantitative.lipschitz x hx t ht C hC

/-- The actual recursive family has the complete collection of properties. -/
theorem recursiveLiftCandidate_full_properties (B : TensorBackground V) (n : ℕ) :
    FullSmoothTensorLiftProperties B n (recursiveLiftCandidate B n) (liftMetricConstant n) where
  complete := recursiveLiftCandidate_complete B n
  separable := recursiveLiftCandidate_separable B n
  finiteDimensional := fun hV => recursiveLiftCandidate_finiteDimensional B hV n
  qualitative := recursiveLiftCandidate_properties B n
  quantitative := recursiveLiftCandidate_metric_properties B n

theorem exists_full_smooth_tensor_lift (B : TensorBackground V) (n : ℕ) :
    ∃ L : LiftCandidate B n, FullSmoothTensorLiftProperties B n L (liftMetricConstant n) :=
  ⟨recursiveLiftCandidate B n, recursiveLiftCandidate_full_properties B n⟩

end FixedSpace

/-- Nonnegativity follows from the scalar recursion alone. -/
theorem liftMetricConstant_nonneg (n : ℕ) : 0 ≤ liftMetricConstant n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [liftMetricConstant_eq]
    split_ifs with hn
    · exact le_rfl
    · apply stepMetricConstant_nonneg n
      intro k hk
      simpa only [if_pos hk] using ih k hk

/-- The scalar sequence is chosen before the Hilbert space, so the constants
depend only on particle number. Neither local lifts nor an induction step
are among the hypotheses. -/
theorem full_smooth_tensor_lift :
    ∃ b : ℕ → ℝ,
      (∀ n, 0 ≤ b n) ∧
      ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]
        (B : TensorBackground V) (n : ℕ),
        ∃ L : LiftCandidate B n, FullSmoothTensorLiftProperties B n L (b n) := by
  refine ⟨liftMetricConstant, liftMetricConstant_nonneg, ?_⟩
  intro V _ _ _ B n
  exact exists_full_smooth_tensor_lift B n

end GptLean.SymmetricLift
