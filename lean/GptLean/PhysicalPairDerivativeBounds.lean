import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
Coordinate estimates for the full derivative on a Euclidean domain.
These turn the actual weak-coordinate graph norm into the operator-valued
L2 derivative estimate needed by the Hilbert-valued Sobolev inequality.
-/

noncomputable section

namespace GptLean.PhysicalPairDerivativeBounds

open MeasureTheory
open scoped ENNReal

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite coordinate bound for the actual operator norm. -/
theorem norm_le_sum_coordinates (T : EuclideanSpace ℝ I →L[ℝ] E) :
    ‖T‖ ≤ ∑ i, ‖T (EuclideanSpace.single i 1)‖ := by
  apply T.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have hx : ∑ i, x i • EuclideanSpace.single i 1 = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun I ℝ).sum_repr x
  calc
    ‖T x‖ = ‖∑ i, x i • T (EuclideanSpace.single i 1)‖ := by
      conv_lhs => rw [← hx, map_sum]
      simp only [map_smul]
    _ ≤ ∑ i, ‖x i • T (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖T (EuclideanSpace.single i 1)‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = (∑ i, ‖T (EuclideanSpace.single i 1)‖) * ‖x‖ :=
      (Finset.sum_mul ..).symm

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The operator-valued Lp norm is bounded by the sum of coordinate Lp norms. -/
theorem eLpNorm_le_sum_coordinates {p : ℝ≥0∞} (hp : 1 ≤ p)
    (T : X → EuclideanSpace ℝ I →L[ℝ] E)
    (hT : ∀ i, AEStronglyMeasurable (fun x => T x (EuclideanSpace.single i 1)) μ) :
    eLpNorm T p μ ≤ ∑ i, eLpNorm (fun x => T x (EuclideanSpace.single i 1)) p μ := by
  calc
    eLpNorm T p μ ≤ eLpNorm (fun x => ∑ i, ‖T x (EuclideanSpace.single i 1)‖) p μ :=
      eLpNorm_mono_real (fun x => norm_le_sum_coordinates (T x))
    _ ≤ ∑ i, eLpNorm (fun x => ‖T x (EuclideanSpace.single i 1)‖) p μ := by
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (s := Finset.univ) (fun i _ => (hT i).norm) hp)
    _ = _ := by simp only [eLpNorm_norm]

/-- A uniform bound on the L2 coordinate classes gives a finite-dimensional
constant for the operator-valued derivative, with no new graph assumption. -/
theorem eLpNorm_le_card_mul {T : X → EuclideanSpace ℝ I →L[ℝ] E}
    (d : I → Lp E 2 μ)
    (hT : ∀ i, (fun x => T x (EuclideanSpace.single i 1)) =ᵐ[μ] d i)
    {C : ℝ} (hC : ∀ i, ‖d i‖ ≤ C) :
    eLpNorm T 2 μ ≤ Fintype.card I * ENNReal.ofReal C := by
  calc
    eLpNorm T 2 μ ≤ ∑ i, eLpNorm (fun x => T x (EuclideanSpace.single i 1)) 2 μ :=
      eLpNorm_le_sum_coordinates (by norm_num) T
        (fun i => (Lp.aestronglyMeasurable (d i)).congr (hT i).symm)
    _ = ∑ i, ENNReal.ofReal ‖d i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [eLpNorm_congr_ae (hT i), ← Lp.enorm_def, ← ofReal_norm]
    _ ≤ ∑ _i : I, ENNReal.ofReal C :=
      Finset.sum_le_sum (fun i _ => ENNReal.ofReal_le_ofReal (hC i))
    _ = _ := by simp [nsmul_eq_mul]

end GptLean.PhysicalPairDerivativeBounds
