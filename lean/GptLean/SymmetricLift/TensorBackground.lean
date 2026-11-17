import GptLean.SymmetricLift.CoincidenceBlocks
import GptLean.SymmetricLift.CompletedTensor
import Mathlib.Tactic.Linarith

/-!
Explicit standard background for completed finite Hilbert tensor powers.

These fields describe only Hilbert tensor powers, their canonical permutation
representations, symmetric projections and fixed regrouping isometries.
Regrouping depends only on the coincidence partition of the configuration.
These fields contain no local lift maps, smooth partitions, derivative
estimates, or induction steps for the article's lift.
The completion and smooth transport used with these fixed isometries are
proved in `CompletedTensor`, and finite operator tensorization in `Induction`.
-/

noncomputable section

namespace GptLean.SymmetricLift

open UniformSpace TopologicalSpace
open scoped BigOperators

/-- Fix one ordering of all distinct coincidence classes. -/
def coincidenceBlockList {N : ℕ} (x : Configuration N) : List (PositionClasses x) := by
  classical
  exact (Finset.univ : Finset (PositionClasses x)).toList

abbrev blockSize {N : ℕ} (x : Configuration N) (c : PositionClasses x) : ℕ :=
  Fintype.card (ClassBlock x c)

abbrev ChartBlockDomain (H : ℕ → Type)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    {N : ℕ} (x : Configuration N) : TensorHilbert :=
  BlockTensor (fun c : PositionClasses x => H (blockSize x c)) (coincidenceBlockList x)

/-- Standard tensor-space data, independent of the tensor-lift construction. -/
structure TensorBackground (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [SeparableSpace V] where
  H : ℕ → TensorHilbert
  complete : ∀ n, CompleteSpace (H n)
  separable : ∀ n, SeparableSpace (H n)
  finiteDimensional : ∀ n, FiniteDimensional ℂ V → FiniteDimensional ℂ (H n)
  R : ∀ n, Equiv.Perm (Fin n) →* ((H n) ≃ₗᵢ[ℂ] (H n))
  P : ∀ n, (H n) →L[ℂ] (H n)
  projection_idempotent : ∀ n u, P n (P n u) = P n u
  projection_orthogonal : ∀ n u v, inner ℂ (P n u) (v - P n v) = 0
  projection_left : ∀ n π u, P n (R n π u) = P n u
  projection_right : ∀ n π u, R n π (P n u) = P n u
  projection_small : ∀ n, n ≤ 1 → P n = ContinuousLinearMap.id ℂ (H n)
  pure : ∀ n, (Fin n → V) → H n
  pure_unit : ∀ n t, (∀ i, ‖t i‖ = 1) → ‖pure n t‖ = 1
  pure_permutation : ∀ n (π : Equiv.Perm (Fin n)) t,
    pure n (fun i => t (π.symm i)) = R n π (pure n t)
  pure_diagonal_fixed : ∀ n v, P n (pure n (fun _ => v)) = pure n (fun _ => v)
  pure_telescope : ∀ n t s, (∀ i, ‖t i‖ = 1) → (∀ i, ‖s i‖ = 1) →
    ‖pure n t - pure n s‖ ≤ ∑ i, ‖t i - s i‖
  regroup : ∀ {n} (x : Configuration n),
    H n ≃ₗᵢ[ℂ] Completion (ChartBlockDomain (fun m => H m) x)
  regroup_pure : ∀ {n} (x : Configuration n) t,
    regroup x (pure n t) =
      (blockTensorVector (fun c : PositionClasses x => H (blockSize x c))
        (fun c => pure (blockSize x c) (fun j => t (((blockEnumeration x c).symm j).val)))
        (coincidenceBlockList x) : Completion (ChartBlockDomain (fun m => H m) x))
  regroup_permutation : ∀ {n} (x : Configuration n) (π : Equiv.Perm (Fin n))
      (hπ : permuteConfiguration π x = x) (u : H n),
    regroup x (R n π u) =
      (blockTensorFamily (fun c : PositionClasses x => H (blockSize x c))
        (fun c : PositionClasses x => H (blockSize x c))
        (fun c (_ : ℝ) => (R (blockSize x c) (indexedBlockPermutation π x hπ c)).toLinearIsometry.toContinuousLinearMap)
        (coincidenceBlockList x) 0).completion (regroup x u)
  regroup_projection : ∀ {n} (x : Configuration n) (u : H n),
    (blockTensorFamily (fun c : PositionClasses x => H (blockSize x c))
      (fun c : PositionClasses x => H (blockSize x c))
      (fun c (_ : ℝ) => P (blockSize x c)) (coincidenceBlockList x) 0).completion
        (regroup x (P n u)) = regroup x (P n u)

attribute [instance] TensorBackground.complete TensorBackground.separable

namespace TensorBackground

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]
variable (B : TensorBackground V)

/-- Contractivity of the complementary projection is derived from orthogonality. -/
theorem remainder_norm_le (n : ℕ) (u : B.H n) : ‖u - B.P n u‖ ≤ ‖u‖ := by
  have he := norm_add_sq (𝕜 := ℂ) (B.P n u) (u - B.P n u)
  have hsum : B.P n u + (u - B.P n u) = u := by abel
  rw [hsum, B.projection_orthogonal, map_zero, mul_zero, add_zero] at he
  nlinarith [norm_nonneg (u - B.P n u), norm_nonneg u, sq_nonneg ‖B.P n u‖]

theorem remainder_norm_le_distance (n : ℕ) (u s : B.H n) (hs : B.P n s = s) :
    ‖u - B.P n u‖ ≤ ‖u - s‖ := by
  have h := B.remainder_norm_le n (u - s)
  have he : u - s - B.P n (u - s) = u - B.P n u := by rw [map_sub, hs]; abel
  rw [he] at h
  exact h

/-- The quantitative near-symmetry used at total coincidence comes from
the ordinary tensor telescoping inequality and the orthogonal projection. -/
theorem pure_remainder_bound (n : ℕ) (t : Fin n → V) (v : V)
    (ht : ∀ i, ‖t i‖ = 1) (hv : ‖v‖ = 1) :
    ‖B.pure n t - B.P n (B.pure n t)‖ ≤ ∑ i, ‖t i - v‖ :=
  (B.remainder_norm_le_distance n _ _ (B.pure_diagonal_fixed n v)).trans
    (B.pure_telescope n t (fun _ => v) ht (fun _ => hv))

end TensorBackground

end GptLean.SymmetricLift
