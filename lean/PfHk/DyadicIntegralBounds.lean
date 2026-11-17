import PfHk.DyadicFractional

/-! Integration of weighted annular families. The hypotheses are pointwise
cutoff bounds and overlap bounds. No Carleman endpoint is assumed. -/

noncomputable section
namespace PfHk.DyadicFractional

open MeasureTheory
attribute [local instance] Classical.propDecidable

set_option Elab.async false
set_option maxHeartbeats 80000

variable {X J : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Integrate an actual finite weighted sum of nonnegative densities. -/
theorem finite_weighted_integral_bound (S : Finset J) (c : J → ℝ)
    (q : J → X → ℝ) (f : X → ℝ)
    (hq : ∀ j ∈ S, Integrable (q j) μ) (hf : Integrable f μ)
    (hsum : ∀ᵐ x ∂μ, (∑ j ∈ S, c j * q j x) ≤ f x) :
    (∑ j ∈ S, c j * ∫ x, q j x ∂μ) ≤ ∫ x, f x ∂μ := by
  calc
    _ = ∫ x, ∑ j ∈ S, c j * q j x ∂μ := by
      rw [integral_finsetSum _ (fun j hj => (hq j hj).const_mul (c j))]
      simp only [integral_const_mul]
    _ ≤ _ := integral_mono_ae
      (integrable_finsetSum _ (fun j hj => (hq j hj).const_mul (c j))) hf hsum

/-- A pointwise weighted annular envelope gives its finite-sum envelope.
The right hand side uses the number of annuli containing the point. -/
theorem weighted_sum_le_of_overlap (S : Finset J) (A : J → Set X)
    (c : J → ℝ) (q : J → X → ℝ) (f : X → ℝ) {K m : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x, 0 ≤ f x)
    (hout : ∀ j ∈ S, ∀ x ∉ A j, q j x = 0)
    (hbound : ∀ j ∈ S, ∀ x ∈ A j, c j * q j x ≤ K * f x)
    (hoverlap : ∀ x, (∑ j ∈ S, (A j).indicator (fun _ => (1 : ℝ)) x) ≤ m) :
    ∀ x, (∑ j ∈ S, c j * q j x) ≤ (m * K) * f x := by
  intro x
  calc
    _ ≤ ∑ j ∈ S, (A j).indicator (fun _ => (1 : ℝ)) x * (K * f x) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hx : x ∈ A j
      · simpa only [Set.indicator_of_mem hx, one_mul] using hbound j hj x hx
      · simp only [hout j hj x hx, mul_zero, Set.indicator_of_notMem hx, zero_mul,
          le_refl]
    _ = (∑ j ∈ S, (A j).indicator (fun _ => (1 : ℝ)) x) * (K * f x) :=
      (Finset.sum_mul ..).symm
    _ ≤ m * (K * f x) := mul_le_mul_of_nonneg_right (hoverlap x)
      (mul_nonneg hK (hf x))
    _ = _ := by ring

/-- The weighted sum of actual annular integrals is bounded by the
overlap constant times its common pointwise envelope. -/
theorem weighted_annular_sum_le (S : Finset J) (A : J → Set X)
    (c : J → ℝ) (q : J → X → ℝ) (f : X → ℝ) {K m : ℝ}
    (hK : 0 ≤ K) (hf0 : ∀ x, 0 ≤ f x)
    (hq : ∀ j ∈ S, Integrable (q j) μ) (hf : Integrable f μ)
    (hout : ∀ j ∈ S, ∀ x ∉ A j, q j x = 0)
    (hbound : ∀ j ∈ S, ∀ x ∈ A j, c j * q j x ≤ K * f x)
    (hoverlap : ∀ x, (∑ j ∈ S, (A j).indicator (fun _ => (1 : ℝ)) x) ≤ m) :
    (∑ j ∈ S, c j * ∫ x, q j x ∂μ) ≤ (m * K) * ∫ x, f x ∂μ := by
  exact (finite_weighted_integral_bound S c q (fun x => (m * K) * f x)
    hq (hf.const_mul _) (ae_of_all _
      (weighted_sum_le_of_overlap S A c q f hK hf0 hout hbound hoverlap))).trans_eq
      (integral_const_mul _ _)

/-- The characteristic-function overlap bound is exactly the cardinal
bound for the active annuli. -/
theorem overlap_sum_eq_card (S : Finset J) (A : J → Set X) (x : X) :
    (∑ j ∈ S, (A j).indicator (fun _ => (1 : ℝ)) x) =
      ((S.filter fun j => x ∈ A j).card : ℝ) := by
  classical
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hx : x ∈ A j <;> simp [hx]

/-- Uniform finite annular bounds also give the countable sum, including
summability. Thus no truncation remains in the fractional conclusion. -/
theorem fractional_tsum {H : Type*} [NormedAddCommGroup H]
    (w Lw fractional : J → H) (β R : J → ℝ)
    {τ s C₀ C₂ F : ℝ} (hτ : 0 < τ) (hs : 0 ≤ s) (hs2 : s ≤ 2)
    (hβ : ∀ j, 0 < β j) (hR : ∀ j, 0 < R j)
    (hspectral : ∀ j, ‖fractional j‖ ^ 2 ≤
      (‖Lw j‖ ^ 2) ^ (s / 2) * (‖w j‖ ^ 2) ^ (1 - s / 2))
    (hzero : ∀ S : Finset J, (∑ j ∈ S,
      coefficient τ (β j) (R j) 0 * ‖w j‖ ^ 2) ≤ C₀ * F)
    (hsecond : ∀ S : Finset J, (∑ j ∈ S,
      coefficient τ (β j) (R j) 2 * ‖Lw j‖ ^ 2) ≤ C₂ * F) :
    Summable (fun j => coefficient τ (β j) (R j) s * ‖fractional j‖ ^ 2) ∧
      (∑' j, coefficient τ (β j) (R j) s * ‖fractional j‖ ^ 2) ≤
        ((s / 2) * C₂ + (1 - s / 2) * C₀) * F := by
  have hnonneg : ∀ j, 0 ≤ coefficient τ (β j) (R j) s * ‖fractional j‖ ^ 2 :=
    fun j => mul_nonneg (coefficient_pos hτ (hβ j) (hR j) s).le (sq_nonneg _)
  have hbound (S : Finset J) := fractional_sum S w Lw fractional β R hτ hs hs2
    (fun j _ => hβ j) (fun j _ => hR j) (fun j _ => hspectral j) (hzero S) (hsecond S)
  exact ⟨summable_of_sum_le hnonneg hbound, Real.tsum_le_of_sum_le hnonneg hbound⟩

end PfHk.DyadicFractional
