import PfHk.SmoothDyadicCutoffs
import PfHk.CarlemanWeightDerivatives

/-! Uniform logarithmic weight comparisons on the actual dyadic annuli. -/

noncomputable section
namespace PfHk.SmoothDyadicCutoffs

open PfHk.CarlemanWeights Metric
set_option Elab.async false
set_option maxHeartbeats 60000
attribute [local instance] Classical.propDecidable

/-- Comparison of `β` at two cylinder coordinates that differ by at most a
factor two and by at most two units, valid for every positive exponent once
the coordinate dominates the exponent. The quadratic part of the power uses
the factor two and the remaining power uses the additive gap. -/
theorem beta_doubling {α t u : ℝ} (hα : 0 < α)
    (ht : 0 < t) (hu : 0 < u) (htu : t ≤ 2 * u) (hgap : t ≤ u + 2)
    (hαu : 4 * α ≤ u) : beta α u ≤ 8 * beta α t := by
  have hsq : u ^ (-2 : ℝ) ≤ 4 * t ^ (-2 : ℝ) := by
    have hmon := Real.rpow_le_rpow_of_nonpos ht htu (show (-2 : ℝ) ≤ 0 by norm_num)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hu.le] at hmon
    have h4 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
      norm_num
    rw [h4] at hmon
    linarith
  have hexp_half : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.add_one_le_exp (-(1 / 2) : ℝ)
    have hmul : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by
      rw [← Real.exp_add]
      norm_num
    have h' : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by linarith
    have hp := mul_le_mul_of_nonneg_left h' (Real.exp_pos (1 / 2 : ℝ)).le
    linarith
  have hpow : u ^ (-α) ≤ 2 * t ^ (-α) := by
    rw [Real.rpow_def_of_pos hu, Real.rpow_def_of_pos ht]
    have hlog : Real.log t - Real.log u ≤ t / u - 1 := by
      have h := Real.log_le_sub_one_of_pos (div_pos ht hu)
      rwa [Real.log_div ht.ne' hu.ne'] at h
    have hratio : α * (t / u - 1) ≤ 1 / 2 := by
      have h1 : α * (t - u) / u = α * (t / u - 1) := by
        rw [mul_div_assoc, sub_div, div_self hu.ne']
      rw [← h1, div_le_iff₀ hu]
      have h2 := mul_le_mul_of_nonneg_left (show t - u ≤ 2 by linarith) hα.le
      linarith
    have hlogα := mul_le_mul_of_nonneg_left hlog hα.le
    have hexponent : Real.log u * -α ≤ 1 / 2 + Real.log t * -α := by
      linarith
    calc Real.exp (Real.log u * -α)
        ≤ Real.exp (1 / 2 + Real.log t * -α) := Real.exp_le_exp.mpr hexponent
      _ = Real.exp (1 / 2) * Real.exp (Real.log t * -α) := Real.exp_add _ _
      _ ≤ 2 * Real.exp (Real.log t * -α) :=
        mul_le_mul_of_nonneg_right hexp_half (Real.exp_pos _).le
  have hsplit (s : ℝ) (hs : 0 < s) : s ^ (-α - 2) = s ^ (-α) * s ^ (-2 : ℝ) := by
    rw [show -α - 2 = -α + (-2 : ℝ) by ring, Real.rpow_add hs]
  have hc : 0 ≤ α * (α + 1) := by positivity
  have hup : 0 ≤ u ^ (-2 : ℝ) := Real.rpow_nonneg hu.le _
  have htα : 0 ≤ t ^ (-α) := Real.rpow_nonneg ht.le _
  have hprod : u ^ (-α) * u ^ (-2 : ℝ) ≤ (2 * t ^ (-α)) * (4 * t ^ (-2 : ℝ)) :=
    mul_le_mul hpow hsq hup (mul_nonneg (by norm_num) htα)
  have hfinal := mul_le_mul_of_nonneg_left hprod hc
  unfold beta
  rw [hsplit u hu, hsplit t ht]
  exact hfinal.trans_eq (by ring)

theorem logarithmic_annular_comparison {r R : ℝ} (hR : 0 < R)
    (hsmall : R ≤ Real.exp (-2)) (hlo : R / 2 ≤ r) (hhi : r ≤ 2 * R) :
    0 < -Real.log r ∧ 0 < -Real.log R ∧
      -Real.log r ≤ 2 * (-Real.log R) ∧ -Real.log R ≤ 2 * (-Real.log r) := by
  have hr : 0 < r := by linarith
  have hRlog : Real.log R ≤ -2 := by
    simpa only [Real.log_exp] using Real.log_le_log hR hsmall
  have hlogtwo : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    linarith
  have hupper := Real.log_le_log hr hhi
  have hlower := Real.log_le_log (show 0 < R / 2 by positivity) hlo
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hR.ne'] at hupper
  rw [Real.log_div hR.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlower
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem beta_annular_comparison {α r R : ℝ} (hα : 0 < α)
    (hαR : R ≤ Real.exp (-(4 * α + 2)))
    (hR : 0 < R) (hsmall : R ≤ Real.exp (-2)) (hlo : R / 2 ≤ r) (hhi : r ≤ 2 * R) :
    beta α (-Real.log R) ≤ 8 * beta α (-Real.log r) ∧
      beta α (-Real.log r) ≤ 8 * beta α (-Real.log R) := by
  obtain ⟨hr, hR', h₁, h₂⟩ := logarithmic_annular_comparison hR hsmall hlo hhi
  have hr₀ : 0 < r := by linarith
  have hαlog := alpha_threshold_of_radius hR hαR
  have hlogtwo : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    linarith
  have hupper := Real.log_le_log hr₀ hhi
  have hlower := Real.log_le_log (show 0 < R / 2 by positivity) hlo
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hR.ne'] at hupper
  rw [Real.log_div hR.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlower
  exact ⟨beta_doubling hα hr hR' h₁ (by linarith) (by linarith),
    beta_doubling hα hR' hr h₂ (by linarith) (by linarith)⟩

variable {I : Type} [Fintype I] [DecidableEq I]

def dyadicAnnulus (O : EuclideanSpace ℝ I) (R : ℝ) (j : ℕ) : Set (EuclideanSpace ℝ I) :=
  {x | radius R j / 2 ≤ dist x O ∧ dist x O ≤ 2 * radius R j}

theorem dyadicAnnulus_measurable (O : EuclideanSpace ℝ I) (R : ℝ) (j : ℕ) :
    MeasurableSet (dyadicAnnulus O R j) := by
  exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet.inter
    (isClosed_le (continuous_id.dist continuous_const) continuous_const).measurableSet

theorem annulus_overlap_card_le_three (O : EuclideanSpace ℝ I) {R : ℝ} (hR : 0 < R)
    (S : Finset ℕ) (x : EuclideanSpace ℝ I) :
    (S.filter fun j => x ∈ dyadicAnnulus O R j).card ≤ 3 := by
  classical
  let T := S.filter fun j => x ∈ dyadicAnnulus O R j
  by_cases hT : T.Nonempty
  · let a := T.min' hT
    have ha : a ∈ T := Finset.min'_mem _ _
    have hwa : radius R a / 2 ≤ dist x O ∧ dist x O ≤ 2 * radius R a :=
      (Finset.mem_filter.mp ha).2
    have hsub : T ⊆ Finset.Icc a (a + 2) := by
      intro j hj
      have haj : a ≤ j := Finset.min'_le _ _ hj
      have hwj : radius R j / 2 ≤ dist x O ∧ dist x O ≤ 2 * radius R j :=
        (Finset.mem_filter.mp hj).2
      have hja : j < a + 3 := by
        by_contra! hja
        have hrj := radius_antitone hR.le hja
        rw [radius_add_three] at hrj
        linarith [radius_pos hR a]
      exact Finset.mem_Icc.mpr ⟨haj, by omega⟩
    exact (Finset.card_le_card hsub).trans_eq (by simp; omega)
  · have hz : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    change T.card ≤ 3
    rw [hz]
    simp

/-- Finite overlap sums pointwise bounds without taking a supremum of
the exponential weight on any annulus. -/
theorem sum_le_three_of_annular_bound (O : EuclideanSpace ℝ I) {R : ℝ} (hR : 0 < R)
    (S : Finset ℕ) (x : EuclideanSpace ℝ I) (v : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ j ∈ S, x ∉ dyadicAnnulus O R j → v j = 0)
    (hbound : ∀ j ∈ S, x ∈ dyadicAnnulus O R j → v j ≤ B) :
    (∑ j ∈ S, v j) ≤ 3 * B := by
  classical
  let T := S.filter fun j => x ∈ dyadicAnnulus O R j
  have hsum : (∑ j ∈ S, v j) = ∑ j ∈ T, v j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hx : x ∈ dyadicAnnulus O R j
    · simp [hx]
    · simp [hx, hzero j hj hx]
  rw [hsum]
  calc
    _ ≤ ∑ _ ∈ T, B := Finset.sum_le_sum fun j hj =>
      hbound j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
    _ = (T.card : ℝ) * B := by simp
    _ ≤ 3 * B := mul_le_mul_of_nonneg_right
      (by exact_mod_cast annulus_overlap_card_le_three O hR S x) hB

end PfHk.SmoothDyadicCutoffs
