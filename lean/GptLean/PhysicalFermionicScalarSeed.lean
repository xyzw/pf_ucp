import GptLean.PhysicalElectronicFermions
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
A nonzero smooth compactly supported scalar with the fermionic sign
character, on the actual electronic configuration space. The determinant
is multiplied by a finite permutation product of ordinary smooth bumps.
No existence of a fermionic test state is assumed.
-/

noncomputable section

namespace GptLean.PhysicalFermionicScalarSeed

open SymmetricLift MeasureTheory Filter Topology
open scoped BigOperators ContDiff

variable (N : ℕ)

def seedPoint : Configuration N :=
  WithLp.toLp 2 (fun p : Fin N × Fin 3 => if p.2 = 0 then (p.1.val : ℝ) else 0)

@[simp] theorem seedPoint_first (i : Fin N) : seedPoint N (i, 0) = (i.val : ℝ) := by
  simp [seedPoint]

def alternant (x : Configuration N) : ℝ :=
  (Matrix.vandermonde (fun i : Fin N => x (i, 0))).det

theorem alternant_smooth : ContDiff ℝ ∞ (alternant N) := by
  unfold alternant
  simp only [Matrix.det_apply', Matrix.vandermonde_apply]
  apply ContDiff.sum
  intro π _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N × Fin 3 => ℝ) (π i, 0)).contDiff.pow i.val

theorem alternant_permute (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    alternant N (permuteConfiguration π x) =
      (Equiv.Perm.sign π : ℝ) * alternant N x := by
  have hmatrix : Matrix.vandermonde (fun i : Fin N => permuteConfiguration π x (i, 0)) =
      (Matrix.vandermonde (fun i : Fin N => x (i, 0))).submatrix π.symm id := by
    ext i j
    rfl
  unfold alternant
  rw [hmatrix, Matrix.det_permute]
  simp

theorem alternant_seedPoint_ne_zero : alternant N (seedPoint N) ≠ 0 := by
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j hij
  simp only [seedPoint_first] at hij
  exact Fin.ext (by exact_mod_cast hij)

def bump : ContDiffBump (0 : Configuration N) where
  rIn := ‖seedPoint N‖ + 1
  rOut := ‖seedPoint N‖ + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def symmetricBump (x : Configuration N) : ℝ :=
  ∏ π : Equiv.Perm (Fin N), bump N (permuteConfiguration π x)

theorem symmetricBump_smooth : ContDiff ℝ ∞ (symmetricBump N) := by
  apply contDiff_prod
  intro π _
  exact (bump N).contDiff.comp (permuteConfiguration π).toContinuousLinearEquiv.contDiff

theorem symmetricBump_permute (σ : Equiv.Perm (Fin N)) (x : Configuration N) :
    symmetricBump N (permuteConfiguration σ x) = symmetricBump N x := by
  unfold symmetricBump
  apply Fintype.prod_equiv (Equiv.mulRight σ)
  intro π
  change bump N (permuteConfiguration π (permuteConfiguration σ x)) =
    bump N (permuteConfiguration (π * σ) x)
  rw [permuteConfiguration_mul]

theorem symmetricBump_compact : HasCompactSupport (symmetricBump N) := by
  rw [hasCompactSupport_iff_eventuallyEq] at *
  have h := (hasCompactSupport_iff_eventuallyEq.mp (bump N).hasCompactSupport)
  filter_upwards [h] with x hx
  change (∏ π : Equiv.Perm (Fin N), bump N (permuteConfiguration π x)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : Equiv.Perm (Fin N)))
  simpa using hx

theorem symmetricBump_seedPoint : symmetricBump N (seedPoint N) = 1 := by
  apply Finset.prod_eq_one
  intro π _
  apply (bump N).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, (permuteConfiguration π).norm_map]
  change ‖seedPoint N‖ ≤ ‖seedPoint N‖ + 1
  linarith

def scalar (x : Configuration N) : ℝ := alternant N x * symmetricBump N x

theorem scalar_smooth : ContDiff ℝ ∞ (scalar N) :=
  (alternant_smooth N).mul (symmetricBump_smooth N)

theorem scalar_compact : HasCompactSupport (scalar N) :=
  (symmetricBump_compact N).mul_left

theorem scalar_permute (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    scalar N (permuteConfiguration π x) = (Equiv.Perm.sign π : ℝ) * scalar N x := by
  rw [scalar, alternant_permute, symmetricBump_permute, scalar, mul_assoc]

theorem scalar_seedPoint_ne_zero : scalar N (seedPoint N) ≠ 0 := by
  simpa [scalar, symmetricBump_seedPoint] using alternant_seedPoint_ne_zero N

theorem scalar_ne_zero : scalar N ≠ 0 := by
  intro h
  exact scalar_seedPoint_ne_zero N (congrFun h (seedPoint N))

end GptLean.PhysicalFermionicScalarSeed
