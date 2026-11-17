import GptLean.SymmetricLift.TensorBackground
import GptLean.SymmetricLift.MetricGeometry
import Mathlib.Tactic.FieldSimp

/-!
The actual near-symmetry estimate in Step 4. The tensor telescoping inequality
is standard Hilbert tensor background. The configuration geometry and all
radius cancellation and minimum estimates below are proved here.
-/

noncomputable section

namespace GptLean.SymmetricLift

open TopologicalSpace
open scoped BigOperators NNReal

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]

def configurationTensor (B : TensorBackground V) (t : EuclideanSpace ℝ (Fin 3) → V)
    {N : ℕ} (x : Configuration N) : B.H N := B.pure N (fun i => t (particle x i))

def symmetryRemainder (B : TensorBackground V) (t : EuclideanSpace ℝ (Fin 3) → V)
    {N : ℕ} (x : Configuration N) : ℝ :=
  ‖configurationTensor B t x - B.P N (configurationTensor B t x)‖

theorem symmetryRemainder_nonneg (B : TensorBackground V)
    (t : EuclideanSpace ℝ (Fin 3) → V) {N : ℕ} (x : Configuration N) :
    0 ≤ symmetryRemainder B t x := norm_nonneg _

theorem symmetryRemainder_le_one (B : TensorBackground V)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1)
    {N : ℕ} (x : Configuration N) : symmetryRemainder B t x ≤ 1 := by
  calc
    _ ≤ ‖configurationTensor B t x‖ := B.remainder_norm_le N (configurationTensor B t x)
    _ = 1 := B.pure_unit _ _ (fun i => ht (particle x i))

theorem symmetryRemainder_le_radius (B : TensorBackground V)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1)
    {L : ℝ≥0} (hL : LipschitzWith L t) {N : ℕ} (x : Configuration N) :
    symmetryRemainder B t x ≤ (N : ℝ) * ‖center N x‖ * (L : ℝ) := by
  calc
    symmetryRemainder B t x ≤ ∑ i, ‖t (particle x i) - t (meanParticle x)‖ :=
      B.pure_remainder_bound N (fun i => t (particle x i)) (t (meanParticle x))
        (fun i => ht (particle x i)) (ht (meanParticle x))
    _ ≤ ∑ _i : Fin N, (L : ℝ) * ‖center N x‖ := by
      apply Finset.sum_le_sum
      intro i _
      have h := hL.dist_le_mul (particle x i) (meanParticle x)
      simp only [dist_eq_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_left (particle_mean_distance_le_radius x i) L.coe_nonneg)
    _ = (N : ℝ) * ‖center N x‖ * (L : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The inverse-pair estimate does not require the one-particle map to be Lipschitz. -/
theorem symmetryRemainder_pair_bound (B : TensorBackground V)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1)
    {N : ℕ} (hN : 2 ≤ N) {x : Configuration N} (hx : x ∈ distinctConfigurations N) :
    (‖center N x‖ ^ 2)⁻¹ * symmetryRemainder B t x ^ 2 ≤ 4 * pairEnergy x := by
  have h0 := symmetryRemainder_nonneg B t x
  have h1 := symmetryRemainder_le_one B t ht x
  have hsq : symmetryRemainder B t x ^ 2 ≤ 1 := by nlinarith
  calc
    _ ≤ (‖center N x‖ ^ 2)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (sq_nonneg _))
    _ ≤ 4 * pairEnergy x := by simpa using radius_inverse_sq_le_pairEnergy hN hx

/-- The radial singularity cancels against the vanishing nonsymmetric part. -/
theorem symmetryRemainder_lipschitz_bound (B : TensorBackground V)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1)
    {L : ℝ≥0} (hL : LipschitzWith L t) {N : ℕ} (hN : 2 ≤ N)
    {x : Configuration N} (hx : x ∈ distinctConfigurations N) :
    (‖center N x‖ ^ 2)⁻¹ * symmetryRemainder B t x ^ 2 ≤ (N : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
  have hr : ‖center N x‖ ≠ 0 := norm_ne_zero_iff.mpr (center_ne_zero_of_distinct hN hx)
  have h := symmetryRemainder_le_radius B t ht hL x
  have hs : symmetryRemainder B t x ^ 2 ≤ ((N : ℝ) * ‖center N x‖ * (L : ℝ)) ^ 2 :=
    (sq_le_sq₀ (symmetryRemainder_nonneg B t x)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) L.coe_nonneg)).mpr h
  calc
    _ ≤ (‖center N x‖ ^ 2)⁻¹ * ((N : ℝ) * ‖center N x‖ * (L : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (sq_nonneg _))
    _ = (N : ℝ) ^ 2 * (L : ℝ) ^ 2 := by field_simp [hr]

/-- The article's minimum estimate, with a harmless nonoptimized constant
depending only on particle number. -/
theorem symmetryRemainder_min_bound (B : TensorBackground V)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1)
    {L : ℝ≥0} (hL : LipschitzWith L t) {N : ℕ} (hN : 2 ≤ N)
    {x : Configuration N} (hx : x ∈ distinctConfigurations N) :
    (‖center N x‖ ^ 2)⁻¹ * symmetryRemainder B t x ^ 2 ≤
      max 4 ((N : ℝ) ^ 2) * min (pairEnergy x) ((L : ℝ) ^ 2) := by
  have hp := (symmetryRemainder_pair_bound B t ht hN hx).trans
    (mul_le_mul_of_nonneg_right (le_max_left 4 ((N : ℝ) ^ 2)) (pairEnergy_nonneg x))
  have hl := (symmetryRemainder_lipschitz_bound B t ht hL hN hx).trans
    (mul_le_mul_of_nonneg_right (le_max_right 4 ((N : ℝ) ^ 2)) (sq_nonneg (L : ℝ)))
  rcases le_total (pairEnergy x) ((L : ℝ) ^ 2) with h | h
  · simpa only [min_eq_left h] using hp
  · simpa only [min_eq_right h] using hl

end GptLean.SymmetricLift
