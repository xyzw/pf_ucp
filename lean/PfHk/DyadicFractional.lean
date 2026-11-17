import PfHk.CarlemanWeights
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Finite annular sums in the mixed electronic and radiation argument.
The vectors and their fractional operator images are actual Hilbert-space
vectors. The interpolation premise is the ordinary positive-operator spectral
inequality. No Pauli–Fierz Carleman estimate is postulated here. -/

noncomputable section
namespace PfHk.DyadicFractional

open MeasureTheory
open scoped ENNReal

set_option maxHeartbeats 80000
set_option Elab.async false

/-- The coefficient in the fractional annular estimate. -/
def coefficient (τ β R s : ℝ) : ℝ := τ ^ (3 - 2 * s) * β * R ^ (2 * s - 2)

theorem coefficient_pos {τ β R : ℝ} (hτ : 0 < τ) (hβ : 0 < β) (hR : 0 < R)
    (s : ℝ) : 0 < coefficient τ β R s := by unfold coefficient; positivity

theorem coefficient_zero (τ β R : ℝ) :
    coefficient τ β R 0 = τ ^ 3 * β / R ^ 2 := by
  norm_num [coefficient, Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv]

theorem coefficient_two (τ β R : ℝ) :
    coefficient τ β R 2 = β * R ^ 2 / τ := by
  norm_num [coefficient, Real.rpow_neg_one, Real.rpow_natCast, div_eq_mul_inv]
  ring

private theorem coefficient_eq_exp {τ β R : ℝ}
    (hτ : 0 < τ) (hβ : 0 < β) (hR : 0 < R) (s : ℝ) :
    coefficient τ β R s =
      Real.exp ((3 - 2 * s) * Real.log τ + Real.log β + (2 * s - 2) * Real.log R) := by
  unfold coefficient
  rw [Real.rpow_def_of_pos hτ, Real.rpow_def_of_pos hR, ← Real.exp_log hβ,
    ← Real.exp_add, ← Real.exp_add, Real.log_exp]
  congr 1
  ring

/-- Exact matching of the two endpoint weights. -/
theorem coefficient_interpolation {τ β R : ℝ}
    (hτ : 0 < τ) (hβ : 0 < β) (hR : 0 < R) (s : ℝ) :
    (coefficient τ β R 2) ^ (s / 2) *
      (coefficient τ β R 0) ^ (1 - s / 2) = coefficient τ β R s := by
  rw [coefficient_eq_exp hτ hβ hR 2, coefficient_eq_exp hτ hβ hR 0,
    coefficient_eq_exp hτ hβ hR s, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- Spectral interpolation and the two endpoint sums imply every mixed
fractional sum. Weighted AM–GM gives a sufficient uniform constant. -/
theorem fractional_sum {J H : Type*} [NormedAddCommGroup H]
    (S : Finset J) (w Lw fractional : J → H) (β R : J → ℝ)
    {τ s C₀ C₂ F : ℝ} (hτ : 0 < τ) (hs : 0 ≤ s) (hs2 : s ≤ 2)
    (hβ : ∀ j ∈ S, 0 < β j) (hR : ∀ j ∈ S, 0 < R j)
    (hspectral : ∀ j ∈ S, ‖fractional j‖ ^ 2 ≤
      (‖Lw j‖ ^ 2) ^ (s / 2) * (‖w j‖ ^ 2) ^ (1 - s / 2))
    (hzero : (∑ j ∈ S, coefficient τ (β j) (R j) 0 * ‖w j‖ ^ 2) ≤ C₀ * F)
    (hsecond : (∑ j ∈ S, coefficient τ (β j) (R j) 2 * ‖Lw j‖ ^ 2) ≤ C₂ * F) :
    (∑ j ∈ S, coefficient τ (β j) (R j) s * ‖fractional j‖ ^ 2) ≤
      ((s / 2) * C₂ + (1 - s / 2) * C₀) * F := by
  have hθ : 0 ≤ s / 2 := by positivity
  have hθ' : 0 ≤ 1 - s / 2 := by linarith
  calc
    _ ≤ ∑ j ∈ S, (
        (s / 2) * (coefficient τ (β j) (R j) 2 * ‖Lw j‖ ^ 2) +
        (1 - s / 2) * (coefficient τ (β j) (R j) 0 * ‖w j‖ ^ 2)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hc₂ := coefficient_pos hτ (hβ j hj) (hR j hj) 2
      have hc₀ := coefficient_pos hτ (hβ j hj) (hR j hj) 0
      have hgm := Real.geom_mean_le_arith_mean2_weighted hθ hθ'
        (mul_nonneg hc₂.le (sq_nonneg ‖Lw j‖))
        (mul_nonneg hc₀.le (sq_nonneg ‖w j‖)) (by ring)
      apply (mul_le_mul_of_nonneg_left (hspectral j hj)
        (coefficient_pos hτ (hβ j hj) (hR j hj) s).le).trans
      calc
        _ = (coefficient τ (β j) (R j) 2 * ‖Lw j‖ ^ 2) ^ (s / 2) *
            (coefficient τ (β j) (R j) 0 * ‖w j‖ ^ 2) ^ (1 - s / 2) := by
          rw [Real.mul_rpow hc₂.le (sq_nonneg ‖Lw j‖),
            Real.mul_rpow hc₀.le (sq_nonneg ‖w j‖),
            ← coefficient_interpolation hτ (hβ j hj) (hR j hj) s]
          ring
        _ ≤ _ := hgm
    _ = (s / 2) * (∑ j ∈ S, coefficient τ (β j) (R j) 2 * ‖Lw j‖ ^ 2) +
        (1 - s / 2) * (∑ j ∈ S, coefficient τ (β j) (R j) 0 * ‖w j‖ ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (s / 2) * (C₂ * F) + (1 - s / 2) * (C₀ * F) :=
      add_le_add (mul_le_mul_of_nonneg_left hsecond hθ)
        (mul_le_mul_of_nonneg_left hzero hθ')
    _ = _ := by ring

/-- The precise radius and parameter gain when an annular multiplier costs
`R²` rather than the mixed coefficient. -/
theorem coefficient_radius_factor {τ β R : ℝ}
    (hτ : 0 < τ) (hβ : 0 < β) (hR : 0 < R) (s : ℝ) :
    R ^ (2 : ℝ) = (R ^ (4 - 2 * s) / β) * τ ^ (-(3 - 2 * s)) *
      coefficient τ β R s := by
  unfold coefficient
  calc
    _ = R ^ ((4 - 2 * s) + (2 * s - 2)) := by congr 1; ring
    _ = R ^ (4 - 2 * s) * R ^ (2 * s - 2) := Real.rpow_add hR _ _
    _ = _ := by
      have ht : τ ^ (-(3 - 2 * s)) * τ ^ (3 - 2 * s) = 1 := by
        rw [← Real.rpow_add hτ]
        simp
      calc
        _ = (R ^ (4 - 2 * s) * R ^ (2 * s - 2)) *
            ((τ ^ (-(3 - 2 * s)) * τ ^ (3 - 2 * s)) * (β / β)) := by
          rw [ht, div_self hβ.ne']
          ring
        _ = _ := by ring

theorem multiplier_sum_bound {J : Type*} (S : Finset J) (β R Q : J → ℝ)
    {τ s σ C F : ℝ} (hτ : 0 < τ) (hσ : 0 ≤ σ)
    (hβ : ∀ j ∈ S, 0 < β j) (hR : ∀ j ∈ S, 0 < R j)
    (hQ : ∀ j ∈ S, 0 ≤ Q j)
    (hratio : ∀ j ∈ S, R j ^ (4 - 2 * s) / β j ≤ σ)
    (hmixed : (∑ j ∈ S, coefficient τ (β j) (R j) s * Q j) ≤ C * F) :
    (∑ j ∈ S, R j ^ (2 : ℝ) * Q j) ≤ σ * τ ^ (-(3 - 2 * s)) * (C * F) := by
  calc
    _ ≤ ∑ j ∈ S, (σ * τ ^ (-(3 - 2 * s))) *
        (coefficient τ (β j) (R j) s * Q j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [coefficient_radius_factor hτ (hβ j hj) (hR j hj) s]
      have hh := mul_le_mul_of_nonneg_right (hratio j hj)
        (mul_nonneg (Real.rpow_nonneg hτ.le (-(3 - 2 * s)))
          (mul_nonneg (coefficient_pos hτ (hβ j hj) (hR j hj) s).le (hQ j hj)))
      convert hh using 1 <;> ring
    _ = (σ * τ ^ (-(3 - 2 * s))) *
        (∑ j ∈ S, coefficient τ (β j) (R j) s * Q j) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmixed (by positivity)

/-- Both endpoint terms in the external magnetic perturbation gain the
same radius ratio `R/β`. This is the mechanism that handles the L6 endpoint. -/
theorem first_order_endpoint_sum {J : Type*} (S : Finset J) (β R Qhigh Qlow : J → ℝ)
    {τ σ Chigh Clow F : ℝ} (hτ : 0 < τ) (hσ : 0 ≤ σ)
    (hβ : ∀ j ∈ S, 0 < β j) (hR : ∀ j ∈ S, 0 < R j)
    (hhigh : ∀ j ∈ S, 0 ≤ Qhigh j) (hlow : ∀ j ∈ S, 0 ≤ Qlow j)
    (hratio : ∀ j ∈ S, R j / β j ≤ σ)
    (hmixedhigh : (∑ j ∈ S, coefficient τ (β j) (R j) (3 / 2) * Qhigh j) ≤ Chigh * F)
    (hmixedlow : (∑ j ∈ S, coefficient τ (β j) (R j) (1 / 2) * Qlow j) ≤ Clow * F) :
    (∑ j ∈ S, (R j ^ 2 * Qhigh j + τ ^ 2 * Qlow j)) ≤ σ * (Chigh + Clow) * F := by
  have hhigh' := multiplier_sum_bound S β R Qhigh (s := 3 / 2) hτ hσ hβ hR hhigh
    (by norm_num; exact hratio) hmixedhigh
  have hlow' : (∑ j ∈ S, τ ^ 2 * Qlow j) ≤ σ * (Clow * F) := by
    calc
      _ ≤ ∑ j ∈ S, σ * (coefficient τ (β j) (R j) (1 / 2) * Qlow j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hid : τ ^ 2 = (R j / β j) * coefficient τ (β j) (R j) (1 / 2) := by
          norm_num [coefficient, Real.rpow_neg_one, Real.rpow_two]
          field_simp [(hβ j hj).ne', (hR j hj).ne'] <;> ring
        rw [hid]
        have hh := mul_le_mul_of_nonneg_right (hratio j hj)
          (mul_nonneg (coefficient_pos hτ (hβ j hj) (hR j hj) (1 / 2)).le (hlow j hj))
        convert hh using 1 <;> ring
      _ = σ * (∑ j ∈ S, coefficient τ (β j) (R j) (1 / 2) * Qlow j) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmixedlow hσ
  rw [Finset.sum_add_distrib]
  have hh := add_le_add hhigh' hlow'
  norm_num [Real.rpow_two] at hh
  exact hh.trans_eq (by ring)

section Integrals

variable {X J : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A telescoping partition with at most `m` nonzero members supplies the
square lower bound needed for localization. No normalization is required. -/
theorem square_lower_of_sum_one (S : Finset J) (η : J → ℝ) {m : ℝ}
    (hsum : (∑ j ∈ S, η j) = 1)
    (hcount : ((S.filter fun j => η j ≠ 0).card : ℝ) ≤ m) :
    1 ≤ m * (∑ j ∈ S, η j ^ 2) := by
  classical
  let T := S.filter fun j => η j ≠ 0
  have hfirst : (∑ j ∈ T, η j) = ∑ j ∈ S, η j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : η j = 0 <;> simp [h]
  have hsecond : (∑ j ∈ T, η j ^ 2) = ∑ j ∈ S, η j ^ 2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : η j = 0 <;> simp [h]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) η
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    hfirst, hsecond, hsum, one_pow] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right hcount
    (Finset.sum_nonneg fun j _ => sq_nonneg (η j)))

/-- A uniform square lower bound suffices for the actual annular source
decomposition. This applies directly to differences of nested scalar bumps. -/
theorem partition_radius_integral_bound_of_lower (S : Finset J) (η : J → X → ℝ)
    (a r g : X → ℝ) (R : J → ℝ) {K m : ℝ} (hm : 0 ≤ m)
    (hg : ∀ x, 0 ≤ g x)
    (hpart : ∀ x, g x ≠ 0 → 1 ≤ m * (∑ j ∈ S, η j x ^ 2))
    (hscale : ∀ j ∈ S, ∀ x, η j x ≠ 0 → r x ^ 2 ≤ K * R j ^ 2)
    (hmeas : AEStronglyMeasurable (fun x => a x ^ 2 * r x ^ 2 * g x) μ)
    (hint : ∀ j ∈ S, Integrable (fun x => η j x ^ 2 * a x ^ 2 * g x) μ) :
    Integrable (fun x => a x ^ 2 * r x ^ 2 * g x) μ ∧
      (∫ x, a x ^ 2 * r x ^ 2 * g x ∂μ) ≤
        (m * K) * (∑ j ∈ S, R j ^ 2 * ∫ x, η j x ^ 2 * a x ^ 2 * g x ∂μ) := by
  let f := fun x => a x ^ 2 * r x ^ 2 * g x
  let b := fun x => ∑ j ∈ S, K * R j ^ 2 * (η j x ^ 2 * a x ^ 2 * g x)
  have hb : Integrable b μ := integrable_finsetSum _ fun j hj => (hint j hj).const_mul _
  have hf0 (x : X) : 0 ≤ f x := mul_nonneg
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hg x)
  have hle (x : X) : f x ≤ m * b x := by
    have hstart : f x ≤ m * (∑ j ∈ S, r x ^ 2 * (η j x ^ 2 * a x ^ 2 * g x)) := by
      by_cases hz : g x = 0
      · simp [f, hz]
      · have hh := mul_le_mul_of_nonneg_right (hpart x hz) (hf0 x)
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
    · exact mul_le_mul_of_nonneg_right (hscale j hj x hη)
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hg x))
  have hf : Integrable f μ := (hb.const_mul m).mono' hmeas (by
    filter_upwards [] with x
    simpa only [Real.norm_of_nonneg (hf0 x)] using hle x)
  refine ⟨hf, (integral_mono_ae hf (hb.const_mul m) (ae_of_all _ hle)).trans_eq ?_⟩
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

/-- A square partition and annular radius comparison control an actual
weighted source integral by its localized integrals. Taking `g = ‖Wu‖²`
and `a = exp (τ φ)` gives the scalar multiplier decomposition. -/
theorem partition_radius_integral_bound (S : Finset J) (η : J → X → ℝ)
    (a r g : X → ℝ) (R : J → ℝ) {K : ℝ}
    (hg : ∀ x, 0 ≤ g x)
    (hpart : ∀ x, g x ≠ 0 → (∑ j ∈ S, η j x ^ 2) = 1)
    (hscale : ∀ j ∈ S, ∀ x, η j x ≠ 0 → r x ^ 2 ≤ K * R j ^ 2)
    (hmeas : AEStronglyMeasurable (fun x => a x ^ 2 * r x ^ 2 * g x) μ)
    (hint : ∀ j ∈ S, Integrable (fun x => η j x ^ 2 * a x ^ 2 * g x) μ) :
    Integrable (fun x => a x ^ 2 * r x ^ 2 * g x) μ ∧
      (∫ x, a x ^ 2 * r x ^ 2 * g x ∂μ) ≤
        K * (∑ j ∈ S, R j ^ 2 * ∫ x, η j x ^ 2 * a x ^ 2 * g x ∂μ) := by
  simpa only [one_mul] using partition_radius_integral_bound_of_lower S η a r g R
    (m := 1) zero_le_one hg (fun x hx => by rw [hpart x hx]; norm_num)
    hscale hmeas hint

/-- Bounded overlap is a scalar count of annuli. It controls the actual
sum of their nonnegative energy integrals. -/
theorem annular_sum_le (S : Finset J) (A : J → Set X) (f : X → ℝ)
    (hA : ∀ j ∈ S, MeasurableSet (A j)) (hf : Integrable f μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) {m : ℝ}
    (hoverlap : ∀ᵐ x ∂μ, (∑ j ∈ S, (A j).indicator (fun _ => (1 : ℝ)) x) ≤ m) :
    (∑ j ∈ S, ∫ x in A j, f x ∂μ) ≤ m * ∫ x, f x ∂μ := by
  have hi : ∀ j ∈ S, Integrable ((A j).indicator f) μ :=
    fun j hj => hf.indicator (hA j hj)
  calc
    _ = ∫ x, ∑ j ∈ S, (A j).indicator f x ∂μ := by
      rw [integral_finsetSum _ hi]
      apply Finset.sum_congr rfl
      intro j hj
      exact (integral_indicator (hA j hj)).symm
    _ ≤ ∫ x, m * f x ∂μ := by
      apply integral_mono_ae (integrable_finsetSum _ hi) (hf.const_mul m)
      filter_upwards [hf0, hoverlap] with x hx hm
      have heq : (∑ j ∈ S, (A j).indicator f x) =
          (∑ j ∈ S, (A j).indicator (fun _ => (1 : ℝ)) x) * f x := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : x ∈ A j <;> simp [h]
      rw [heq]
      exact mul_le_mul_of_nonneg_right hm hx
    _ = _ := integral_const_mul _ _

end Integrals
end PfHk.DyadicFractional
