import PfHk.AeDyadicPartition

noncomputable section
namespace PfHk.DyadicWeightedPartition

open MeasureTheory
set_option Elab.async false
set_option maxHeartbeats 20000

variable {X J : Type*} [MeasurableSpace X] {μ : Measure X}

theorem integral_bound (S : Finset J) (η : J → X → ℝ) (w E q : X → ℝ)
    (c : J → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpart : ∀ᵐ x ∂μ, q x ≠ 0 → 1 ≤ m * ∑ j ∈ S, η j x ^ 2)
    (hscale : ∀ᵐ x ∂μ, ∀ j ∈ S, η j x ≠ 0 → w x ≤ c j * E x ^ 2)
    (hi : Integrable (fun x => w x * q x) μ)
    (hint : ∀ j ∈ S, Integrable (fun x => η j x ^ 2 * E x ^ 2 * q x) μ) :
    (∫ x, w x * q x ∂μ) ≤ m * ∑ j ∈ S, c j * ∫ x, η j x ^ 2 * E x ^ 2 * q x ∂μ := by
  have hmajor : Integrable (fun x => m * ∑ j ∈ S, c j * (η j x ^ 2 * E x ^ 2 * q x)) μ :=
    (integrable_finsetSum _ fun j hj => (hint j hj).const_mul _).const_mul _
  have hle : ∀ᵐ x ∂μ, w x * q x ≤ m * ∑ j ∈ S, c j * (η j x ^ 2 * E x ^ 2 * q x) := by
    filter_upwards [hw, hq, hpart, hscale] with x hwx hqx hp hs
    have hstart : w x * q x ≤ m * ∑ j ∈ S, η j x ^ 2 * (w x * q x) := by
      by_cases hz : q x = 0
      · simp [hz]
      · have hh := mul_le_mul_of_nonneg_right (hp hz) (mul_nonneg hwx hqx)
        simpa only [one_mul, mul_assoc, Finset.sum_mul] using hh
    apply hstart.trans
    apply mul_le_mul_of_nonneg_left _ hm
    apply Finset.sum_le_sum
    intro j hj
    by_cases hz : η j x = 0
    · simp [hz]
    · have hh := mul_le_mul_of_nonneg_right (hs j hj hz) (mul_nonneg (sq_nonneg (η j x)) hqx)
      calc
        _ = w x * (η j x ^ 2 * q x) := by ring
        _ ≤ (c j * E x ^ 2) * (η j x ^ 2 * q x) := hh
        _ = _ := by ring
  apply (integral_mono_ae hi hmajor hle).trans_eq
  rw [integral_const_mul, integral_finsetSum _ (fun j hj => (hint j hj).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul]

end PfHk.DyadicWeightedPartition
