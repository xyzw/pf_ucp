import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
Canonical number sectors on a Hilbert direct sum.

The direct sum is Mathlib's actual square-summable space, and the sector
operators are coordinate evaluation followed by coordinate insertion.
The projection laws, completeness of the sector resolution and weighted
number forms follow from this construction.
-/

noncomputable section

namespace GptLean.PhysicalFock

open Filter Topology
open scoped ENNReal InnerProductSpace

variable (K : ℕ → Type*) [∀ n, NormedAddCommGroup (K n)]
  [∀ n, InnerProductSpace ℂ (K n)]

abbrev Space := lp K 2

def sector (n : ℕ) : Space K →L[ℂ] Space K :=
  (lp.singleContinuousLinearMap ℂ K 2 n).comp (lp.evalCLM ℂ K 2 n)

@[simp] theorem sector_apply (n : ℕ) (u : Space K) :
    sector K n u = lp.single 2 n (u n) := rfl

@[simp] theorem sector_coordinate (n : ℕ) (u : Space K) : sector K n u n = u n :=
  lp.single_apply_self _ _ _

theorem sector_coordinate_ne (n m : ℕ) (h : m ≠ n) (u : Space K) :
    sector K n u m = 0 := lp.single_apply_ne _ _ _ h

@[simp] theorem sector_norm (n : ℕ) (u : Space K) : ‖sector K n u‖ = ‖u n‖ :=
  lp.norm_single (by norm_num) _ _

theorem sector_inner (n : ℕ) (u v : Space K) :
    ⟪u, sector K n v⟫_ℂ = ⟪u n, v n⟫_ℂ := lp.inner_single_right _ _ _

theorem sector_idempotent (n : ℕ) : sector K n * sector K n = sector K n := by
  ext u
  simp only [mul_apply_eq_comp, sector_apply, lp.single_apply_self]

theorem sector_orthogonal (n m : ℕ) (h : n ≠ m) : sector K n * sector K m = 0 := by
  ext u
  simp only [mul_apply_eq_comp, sector_apply, zero_apply]
  rw [lp.single_apply_ne _ _ _ h, lp.single_zero]

theorem sector_symmetric (n : ℕ) (u v : Space K) :
    ⟪sector K n u, v⟫_ℂ = ⟪u, sector K n v⟫_ℂ := by
  rw [sector_apply, sector_apply, lp.inner_single_left, lp.inner_single_right]

theorem sector_hasSum (u : Space K) : HasSum (fun n => sector K n u) u :=
  lp.hasSum_single (by norm_num) u

def cutoff (M : ℕ) : Space K →L[ℂ] Space K := ∑ n ∈ Finset.range (M + 1), sector K n

theorem cutoff_tendsto (u : Space K) : Tendsto (fun M => cutoff K M u) atTop (𝓝 u) := by
  have h := (sector_hasSum K u).tendsto_sum_nat
  simpa only [cutoff, sum_apply, Function.comp_def] using
    h.comp (tendsto_add_atTop_nat 1)

omit [∀ n, InnerProductSpace ℂ (K n)] in
theorem coordinate_mass_hasSum (u : Space K) : HasSum (fun n => ‖u n‖ ^ 2) (‖u‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) u

theorem sector_mass_hasSum (u : Space K) : HasSum (fun n => ‖sector K n u‖ ^ 2) (‖u‖ ^ 2) := by
  simpa only [sector_norm] using coordinate_mass_hasSum K u

/-- An unbounded nonnegative weight is retained as an extended-real form. -/
def weightedForm (w : ℕ → ℝ) (u : Space K) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (w n * ‖u n‖ ^ 2)

def numberForm (u : Space K) : ℝ≥0∞ := weightedForm K (fun n => n) u

def weightedTruncation (w : ℕ → ℝ) (M : ℕ) : Space K →L[ℂ] Space K :=
  ∑ n ∈ Finset.range M, (w n : ℂ) • sector K n

theorem weightedTruncation_inner (w : ℕ → ℝ) (M : ℕ) (u : Space K) :
    (⟪u, weightedTruncation K w M u⟫_ℂ).re = ∑ n ∈ Finset.range M, w n * ‖u n‖ ^ 2 := by
  simp only [weightedTruncation, sum_apply, smul_apply, inner_sum,
    inner_smul_right, sector_inner, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem weightedForm_eq_iSup (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (u : Space K) :
    weightedForm K w u = ⨆ M, ENNReal.ofReal (⟪u, weightedTruncation K w M u⟫_ℂ).re := by
  simp only [weightedTruncation_inner]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (hw n) (sq_nonneg _))]
  exact ENNReal.tsum_eq_iSup_nat

theorem numberForm_eq_iSup (u : Space K) :
    numberForm K u = ⨆ M, ENNReal.ofReal
      (⟪u, weightedTruncation K (fun n => n) M u⟫_ℂ).re :=
  weightedForm_eq_iSup K _ (fun n => Nat.cast_nonneg n) u

theorem weightedForm_sector (w : ℕ → ℝ) (n : ℕ) (u : Space K) :
    weightedForm K w (sector K n u) = ENNReal.ofReal (w n * ‖u n‖ ^ 2) := by
  unfold weightedForm
  rw [tsum_eq_single n]
  · rw [sector_coordinate]
  · intro m hmn
    simp only [sector_coordinate_ne K n m hmn, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, ENNReal.ofReal_zero]

theorem numberForm_sector (n : ℕ) (u : Space K) :
    numberForm K (sector K n u) = ENNReal.ofReal ((n : ℝ) * ‖sector K n u‖ ^ 2) := by
  rw [sector_norm]
  exact weightedForm_sector K _ n u

omit [∀ n, InnerProductSpace ℂ (K n)] in
theorem massForm_eq (u : Space K) :
    weightedForm K (fun _ => 1) u = ENNReal.ofReal (‖u‖ ^ 2) := by
  simp only [weightedForm, one_mul]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) (coordinate_mass_hasSum K u).summable,
    (coordinate_mass_hasSum K u).tsum_eq]

/-- Bounded number tests act by the actual weight on each number sector. -/
def boundedWeightOperator (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) :
    Space K →L[ℂ] Space K :=
  LinearMap.mkContinuous
    { toFun u := ⟨fun n => (w n : ℂ) • u n, (lp.memℓp u).norm.mono (fun n => by
        simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hw n))⟩
      map_add' u v := by
        ext n
        change (w n : ℂ) • (u n + v n) = (w n : ℂ) • u n + (w n : ℂ) • v n
        exact smul_add _ _ _
      map_smul' c u := by
        ext n
        change (w n : ℂ) • (c • u n) = c • ((w n : ℂ) • u n)
        exact smul_comm _ _ _ }
    1 (fun u => by
      rw [one_mul]
      apply lp.norm_mono (by norm_num)
      intro n
      change ‖(w n : ℂ) • u n‖ ≤ ‖u n‖
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw n))

@[simp] theorem boundedWeightOperator_apply (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (u : Space K) (n : ℕ) : boundedWeightOperator K w hw u n = (w n : ℂ) • u n := rfl

theorem boundedWeightOperator_hasSum (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (u : Space K) : HasSum (fun n => w n * ‖u n‖ ^ 2)
      (⟪u, boundedWeightOperator K w hw u⟫_ℂ).re := by
  have h := Complex.reCLM.hasSum (lp.hasSum_inner u (boundedWeightOperator K w hw u))
  change HasSum (fun n => (⟪u n, boundedWeightOperator K w hw u n⟫_ℂ).re)
    (⟪u, boundedWeightOperator K w hw u⟫_ℂ).re at h
  have he (n : ℕ) : (⟪u n, boundedWeightOperator K w hw u n⟫_ℂ).re =
      w n * ‖u n‖ ^ 2 := by
    rw [boundedWeightOperator_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  simpa only [he] using h

section Complete

variable [∀ n, CompleteSpace (K n)]

theorem sector_isStarProjection (n : ℕ) : IsStarProjection (sector K n) := by
  refine ⟨sector_idempotent K n, ?_⟩
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact sector_symmetric K n

end Complete

end GptLean.PhysicalFock
