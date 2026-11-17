import GptLean.PhysicalFockTensorSectors
import GptLean.PhysicalFockAnnihilationForm
import GptLean.PhysicalFockSplitContraction

/-!
Actual retained annihilation in the completed tensor sector coordinates.
The coordinate identities hold for every tensor vector by continuity.
Their nonnegative sums retain infinite form values without domain assumptions.
-/

noncomputable section
namespace GptLean.PhysicalFock

open UniformSpace MeasureTheory
open scoped ENNReal InnerProductSpace
open TensorCoordinates TensorSectors

set_option backward.isDefEq.respectTransparency.types false

section TensorMaps
variable {H K E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def firstTensorMap (A : H →L[ℂ] E) : TensorSpace H K →L[ℂ] TensorSpace E K :=
  (A.rTensor K).completion

theorem firstTensorMap_tensor (A : H →L[ℂ] E) (v : H) (w : K) :
    firstTensorMap A (tensor v w) = tensor (A v) w := by
  rw [tensor_apply, firstTensorMap, ContinuousLinearMap.completion_apply_coe]
  rfl

private theorem tensor_clm_ext {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A B : TensorSpace H K →L[ℂ] F)
    (h : ∀ v w, A (tensor v w) = B (tensor v w)) : A = B := by
  apply ContinuousLinearMap.ext
  intro u
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq A.continuous B.continuous
  | ih u =>
    induction u using TensorProduct.induction_on with
    | zero => simp only [Completion.coe_zero, map_zero]
    | tmul v w => exact h v w
    | add u v hu hv => simp only [Completion.coe_add, map_add, hu, hv]

end TensorMaps

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

private theorem pair_retained_operator
    (X : ℕ → Type*) [∀ n, NormedAddCommGroup (X n)]
    [∀ n, InnerProductSpace ℂ (X n)] [∀ n, CompleteSpace (X n)]
    (A : Space X →L[ℂ] Space X) (r m s : ℕ) (D : X m →L[ℂ] X r)
    (hA : ∀ v, A v r = D (v m)) (z : TensorSpace (Space X) (Space X)) :
    pairCoefficients X (retainedOperator A z) (r, s) =
      firstTensorMap D (pairCoefficients X z (m, s)) := by
  let L := (pairCoordinate X (r, s)).comp (retainedOperator A)
  let R := (firstTensorMap D).comp (pairCoordinate X (m, s))
  have hp : ∀ v w : Space X, L (tensor v w) = R (tensor v w) := by
    intro v w
    change pairCoefficients X (retainedOperator A (tensor v w)) (r, s) =
      firstTensorMap D (pairCoefficients X (tensor v w) (m, s))
    rw [retainedOperator_tensor, pairCoefficients_tensor, pairCoefficients_tensor,
      firstTensorMap_tensor]
    exact congrArg (tensor.flip (w s)) (hA v)
  exact congrArg (fun T : TensorSpace (Space X) (Space X) →L[ℂ]
    TensorSpace (X r) (X s) => T z) (tensor_clm_ext L R hp)

theorem pair_retained_annihilationFinite (M r s : ℕ) (hr : r < M)
    (f : Lp ℂ 2 μ) (z : TensorSpace (Fock μ) (Fock μ)) :
    pairCoefficients (Sector μ) (retainedOperator (annihilationFinite μ M f) z) (r, s) =
      firstTensorMap (annihilationSector μ r f) (pairCoefficients (Sector μ) z (r + 1, s)) :=
  pair_retained_operator (Sector μ) (annihilationFinite μ M f) r (r + 1) s
    (annihilationSector μ r f) (fun v =>
      (annihilationFinite_coordinate μ M r f v).trans (ite_eq_left hr)) z

theorem pair_retained_annihilationBlock (r s : ℕ) (f : Lp ℂ 2 μ)
    (z : TensorSpace (Fock μ) (Fock μ)) :
    pairCoefficients (Sector μ) (retainedOperator (annihilationBlock μ r f) z) (r, s) =
      firstTensorMap (annihilationSector μ r f) (pairCoefficients (Sector μ) z (r + 1, s)) :=
  pair_retained_operator (Sector μ) (annihilationBlock μ r f) r (r + 1) s
    (annihilationSector μ r f) (fun v =>
      lp.single_apply_self 2 r (annihilationSector μ r f (v (r + 1)))) z

private theorem pair_retained_zero
    (X : ℕ → Type*) [∀ n, NormedAddCommGroup (X n)]
    [∀ n, InnerProductSpace ℂ (X n)] [∀ n, CompleteSpace (X n)]
    (A : Space X →L[ℂ] Space X) (r s : ℕ) (hA : ∀ v, A v r = 0)
    (z : TensorSpace (Space X) (Space X)) :
    pairCoefficients X (retainedOperator A z) (r, s) = 0 := by
  let L := (pairCoordinate X (r, s)).comp (retainedOperator A)
  let R : TensorSpace (Space X) (Space X) →L[ℂ] TensorSpace (X r) (X s) := 0
  have hp : ∀ v w : Space X, L (tensor v w) = R (tensor v w) := by
    intro v w
    change pairCoefficients X (retainedOperator A (tensor v w)) (r, s) = 0
    rw [retainedOperator_tensor, pairCoefficients_tensor]
    exact (congrArg (tensor.flip (w s)) (hA v)).trans (map_zero _)
  exact congrArg (fun T : TensorSpace (Space X) (Space X) →L[ℂ]
    TensorSpace (X r) (X s) => T z) (tensor_clm_ext L R hp)

theorem pair_retained_annihilationBlock_off (n r s : ℕ) (hr : r ≠ n) (f : Lp ℂ 2 μ)
    (z : TensorSpace (Fock μ) (Fock μ)) :
    pairCoefficients (Sector μ) (retainedOperator (annihilationBlock μ n f) z) (r, s) = 0 :=
  pair_retained_zero (Sector μ) (annihilationBlock μ n f) r s (fun v =>
    lp.single_apply_ne 2 n (annihilationSector μ n f (v (n + 1))) hr) z

private theorem lp_ennreal_norm_sum {ι : Type*} (K : ι → Type*)
    [∀ i, NormedAddCommGroup (K i)] (u : lp K 2) :
    ENNReal.ofReal (‖u‖ ^ 2) = ∑' i, ENNReal.ofReal (‖u i‖ ^ 2) := by
  have hs : HasSum (fun i => ‖u i‖ ^ 2) (‖u‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) u
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hs.summable, hs.tsum_eq]

theorem pair_norm_sum (z : TensorSpace (Fock μ) (Fock μ)) :
    ENNReal.ofReal (‖z‖ ^ 2) = ∑' r, ∑' s,
      ENNReal.ofReal (‖pairCoefficients (Sector μ) z (r, s)‖ ^ 2) := by
  have h := lp_ennreal_norm_sum
    (fun p : ℕ × ℕ => TensorSpace (Sector μ p.1) (Sector μ p.2)) (pairCoefficients (Sector μ) z)
  rw [(pairCoefficients (Sector μ)).norm_map, ENNReal.tsum_prod'] at h
  exact h

private theorem ennreal_norm_sq_zero {V : Type*} [NormedAddCommGroup V]
    (v : V) (h : v = 0) : ENNReal.ofReal (‖v‖ ^ 2) = 0 := by
  rw [h]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero]

private theorem tsum_row_of_zero (t : ℕ → ℕ → ℝ≥0∞) (n : ℕ)
    (h : ∀ r, r ≠ n → ∀ s, t r s = 0) : (∑' r, ∑' s, t r s) = ∑' s, t n s :=
  tsum_eq_single n (fun r hr => (tsum_congr (h r hr)).trans (tsum_zero))

theorem retained_annihilationBlock_norm_sum (n : ℕ) (f : Lp ℂ 2 μ)
    (z : TensorSpace (Fock μ) (Fock μ)) :
    ENNReal.ofReal (‖retainedOperator (annihilationBlock μ n f) z‖ ^ 2) =
      ∑' s, ENNReal.ofReal (‖firstTensorMap (annihilationSector μ n f)
        (pairCoefficients (Sector μ) z (n + 1, s))‖ ^ 2) := by
  let t : ℕ → ℕ → ℝ≥0∞ := fun r s => ENNReal.ofReal
    (‖pairCoefficients (Sector μ) (retainedOperator (annihilationBlock μ n f) z) (r, s)‖ ^ 2)
  have hz : ∀ r, r ≠ n → ∀ s, t r s = 0 := fun r hr s =>
    ennreal_norm_sq_zero _ (pair_retained_annihilationBlock_off μ n r s hr f z)
  have he : (∑' s, t n s) = ∑' s, ENNReal.ofReal
      (‖firstTensorMap (annihilationSector μ n f) (pairCoefficients (Sector μ) z (n + 1, s))‖ ^ 2) :=
    tsum_congr (fun s => congrArg (fun w : TensorSpace (Sector μ n) (Sector μ s) =>
      ENNReal.ofReal (‖w‖ ^ 2)) (pair_retained_annihilationBlock μ n s f z))
  exact (pair_norm_sum μ (retainedOperator (annihilationBlock μ n f) z)).trans
    ((tsum_row_of_zero t n hz).trans he)

def tensorAnnihilationForm (f : Lp ℂ 2 μ) (z : TensorSpace (Fock μ) (Fock μ)) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (‖retainedOperator (annihilationBlock μ n f) z‖ ^ 2)

theorem tensorAnnihilationForm_eq_pairs (f : Lp ℂ 2 μ) (z : TensorSpace (Fock μ) (Fock μ)) :
    tensorAnnihilationForm μ f z = ∑' r, ∑' s,
      ENNReal.ofReal (‖firstTensorMap (annihilationSector μ r f)
        (pairCoefficients (Sector μ) z (r + 1, s))‖ ^ 2) :=
  tsum_congr (fun n => retained_annihilationBlock_norm_sum μ n f z)

end GptLean.PhysicalFock
