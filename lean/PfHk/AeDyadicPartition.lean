import PfHk.DyadicFractional

/-! Annular integral localization with essential support. Both the
partition lower bound and the radius comparison may hold almost everywhere. -/

noncomputable section
namespace PfHk.AeDyadicPartition

open MeasureTheory

set_option Elab.async false
set_option maxHeartbeats 20000

variable {X J : Type*} [MeasurableSpace X] {μ : Measure X}

theorem partition_radius_integral_bound_of_lower (S : Finset J) (η : J → X → ℝ)
    (a r g : X → ℝ) (R : J → ℝ) {K m : ℝ} (hm : 0 ≤ m)
    (hg : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hpart : ∀ᵐ x ∂μ, g x ≠ 0 → 1 ≤ m * (∑ j ∈ S, η j x ^ 2))
    (hscale : ∀ᵐ x ∂μ, ∀ j ∈ S, η j x ≠ 0 → r x ^ 2 ≤ K * R j ^ 2)
    (hmeas : AEStronglyMeasurable (fun x => a x ^ 2 * r x ^ 2 * g x) μ)
    (hint : ∀ j ∈ S, Integrable (fun x => η j x ^ 2 * a x ^ 2 * g x) μ) :
    Integrable (fun x => a x ^ 2 * r x ^ 2 * g x) μ ∧
      (∫ x, a x ^ 2 * r x ^ 2 * g x ∂μ) ≤
        (m * K) * (∑ j ∈ S, R j ^ 2 * ∫ x, η j x ^ 2 * a x ^ 2 * g x ∂μ) := by
  let f := fun x => a x ^ 2 * r x ^ 2 * g x
  let b := fun x => ∑ j ∈ S, K * R j ^ 2 * (η j x ^ 2 * a x ^ 2 * g x)
  have hb : Integrable b μ := integrable_finsetSum _ fun j hj => (hint j hj).const_mul _
  have hf0 : ∀ᵐ x ∂μ, 0 ≤ f x := by
    filter_upwards [hg] with x hx
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hx
  have hle : ∀ᵐ x ∂μ, f x ≤ m * b x := by
    filter_upwards [hg, hf0, hpart, hscale] with x hx hx0 hxpart hxscale
    have hstart : f x ≤ m * (∑ j ∈ S, r x ^ 2 * (η j x ^ 2 * a x ^ 2 * g x)) := by
      by_cases hz : g x = 0
      · simp [f, hz]
      · have hh := mul_le_mul_of_nonneg_right (hxpart hz) hx0
        simp only [one_mul] at hh
        apply hh.trans_eq
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        dsimp [f]
        ring
    apply hstart.trans
    apply mul_le_mul_of_nonneg_left _ hm
    apply Finset.sum_le_sum
    intro j hj
    by_cases hη : η j x = 0
    · simp [hη]
    · exact mul_le_mul_of_nonneg_right (hxscale j hj hη)
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hx)
  have hf : Integrable f μ := (hb.const_mul m).mono' hmeas (by
    filter_upwards [hf0, hle] with x hx0 hxle
    simpa only [Real.norm_of_nonneg hx0] using hxle)
  refine ⟨hf, (integral_mono_ae hf (hb.const_mul m) hle).trans_eq ?_⟩
  rw [integral_const_mul]
  have hbi : (∫ x, b x ∂μ) = K * (∑ j ∈ S, R j ^ 2 *
      ∫ x, η j x ^ 2 * a x ^ 2 * g x ∂μ) := by
    dsimp [b]
    rw [integral_finsetSum _ (fun j hj => (hint j hj).const_mul _), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul]
    ring
  rw [hbi]
  ring

end PfHk.AeDyadicPartition
