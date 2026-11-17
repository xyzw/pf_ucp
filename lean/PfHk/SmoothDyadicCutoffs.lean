import PfHk.SmoothCutoffGeometry
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual dyadic cutoffs from differences of the constructed scalar
bumps. Telescoping and finite overlap replace square normalization. -/

noncomputable section
namespace PfHk.SmoothDyadicCutoffs

open Filter Metric PfHk.SmoothCutoffBounds PfHk.PhysicalCutoffCommutator
open GptLean.ElectronicH1Multiplier
open scoped Topology

set_option maxHeartbeats 20000
set_option Elab.async false

def radius (R : ℝ) (j : ℕ) : ℝ := R / (2 : ℝ) ^ j

theorem radius_pos {R : ℝ} (hR : 0 < R) (j : ℕ) : 0 < radius R j := by
  unfold radius
  positivity

theorem radius_succ (R : ℝ) (j : ℕ) : radius R (j + 1) = radius R j / 2 := by
  unfold radius
  rw [pow_succ, div_mul_eq_div_div]

theorem radius_antitone {R : ℝ} (hR : 0 ≤ R) : Antitone (radius R) := by
  intro j k hjk
  exact div_le_div_of_nonneg_left hR (by positivity : 0 < (2 : ℝ) ^ j)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjk)

theorem radius_add_three (R : ℝ) (j : ℕ) : radius R (j + 3) = radius R j / 8 := by
  unfold radius
  rw [pow_add, div_mul_eq_div_div]
  norm_num

theorem radius_add_five (R : ℝ) (j : ℕ) : radius R (j + 5) = radius R j / 32 := by
  unfold radius
  rw [pow_add, div_mul_eq_div_div]
  norm_num

theorem radius_tendsto (R : ℝ) : Tendsto (radius R) atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => R / (2 : ℝ) ^ j) atTop (𝓝 0)
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul R
  simpa only [radius, one_div, inv_pow, div_eq_mul_inv, mul_zero, one_mul] using h

theorem exists_inner_radius {R ρ : ℝ} (hρ : 0 < ρ) :
    ∃ J : ℕ, 2 * radius R J ≤ ρ := by
  have h : Tendsto (fun j => 2 * radius R j) atTop (𝓝 0) := by
    simpa only [mul_zero] using (radius_tendsto R).const_mul 2
  obtain ⟨J, hJ⟩ := (h.eventually (eventually_lt_nhds hρ)).exists
  exact ⟨J, hJ.le⟩

variable {I : Type} [Fintype I] [DecidableEq I] {x₀ : EuclideanSpace ℝ I}

def cutoff (family : BufferedFamily x₀) (R : ℝ) (j : ℕ) : TwiceDifferentiableMultiplier I :=
  twiceSub (family.cutoff (radius R j)) (family.cutoff (radius R (j + 1)))

theorem family_weight_bounds (family : BufferedFamily x₀) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ I) :
    0 ≤ (family.cutoff r).scalar.weight x ∧ (family.cutoff r).scalar.weight x ≤ 1 := by
  rw [family.weight r hr]
  exact ⟨(bufferedBump I).nonneg, (bufferedBump I).le_one⟩

theorem weight_abs_le_one (family : BufferedFamily x₀) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (x : EuclideanSpace ℝ I) : |(cutoff family R j).scalar.weight x| ≤ 1 := by
  have ho := family_weight_bounds family (radius_pos hR j) x
  have hi := family_weight_bounds family (radius_pos hR (j + 1)) x
  change |(family.cutoff _).scalar.weight x - (family.cutoff _).scalar.weight x| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem weight_telescope (family : BufferedFamily x₀) (R : ℝ) (J : ℕ)
    (x : EuclideanSpace ℝ I) :
    (∑ j ∈ Finset.range J, (cutoff family R j).scalar.weight x) =
      (family.cutoff R).scalar.weight x - (family.cutoff (radius R J)).scalar.weight x := by
  induction J with
  | zero => simp [radius]
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      change ((family.cutoff R).scalar.weight x -
        (family.cutoff (radius R J)).scalar.weight x) +
        ((family.cutoff (radius R J)).scalar.weight x -
          (family.cutoff (radius R (J + 1))).scalar.weight x) = _
      ring

theorem sum_one_on_annulus (family : BufferedFamily x₀) {R ρ : ℝ}
    (hR : 0 < R) (J : ℕ) (hJ : 2 * radius R J ≤ ρ)
    (x : EuclideanSpace ℝ I) (hlo : ρ ≤ dist x x₀) (hhi : dist x x₀ ≤ R) :
    (∑ j ∈ Finset.range J, (cutoff family R j).scalar.weight x) = 1 := by
  rw [weight_telescope, family.weight R hR, family.weight _ (radius_pos hR J),
    buffered_scaled_one hR (by linarith),
    buffered_scaled_zero (radius_pos hR J) (by linarith [radius_pos hR J])]
  norm_num

theorem weight_supported (family : BufferedFamily x₀) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (x : EuclideanSpace ℝ I) (hx : (cutoff family R j).scalar.weight x ≠ 0) :
    radius R j / 2 < dist x x₀ ∧ dist x x₀ < 2 * radius R j := by
  have hr := radius_pos hR j
  have hrs := radius_pos hR (j + 1)
  have heq : (cutoff family R j).scalar.weight x =
      scaled (bufferedBump I) x₀ (radius R j) x -
        scaled (bufferedBump I) x₀ (radius R (j + 1)) x := by
    change (family.cutoff _).scalar.weight x - (family.cutoff _).scalar.weight x = _
    rw [family.weight _ hr, family.weight _ hrs]
  constructor
  · by_contra! hlo
    apply hx
    rw [heq, buffered_scaled_one hr (by linarith),
      buffered_scaled_one hrs (by rw [radius_succ]; linarith)]
    simp
  · by_contra! hhi
    apply hx
    rw [heq, buffered_scaled_zero hr (by linarith),
      buffered_scaled_zero hrs (by rw [radius_succ]; linarith)]
    simp

theorem gradient_bound (family : BufferedFamily x₀) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (i : I) (x : EuclideanSpace ℝ I) :
    |(cutoff family R j).scalar.gradient i x| ≤ 3 * family.firstBound / radius R j := by
  have hr := radius_pos hR j
  change |(scalarSub _ _).gradient i x| ≤ _
  rw [scalarSub_gradient]
  apply (abs_sub _ _).trans
  apply (add_le_add (family.first _ hr i x)
    (family.first _ (radius_pos hR (j + 1)) i x)).trans_eq
  rw [radius_succ]
  field_simp [hr.ne']
  ring

theorem second_gradient_bound (family : BufferedFamily x₀) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (i k : I) (x : EuclideanSpace ℝ I) :
    |((cutoff family R j).derivative i).gradient k x| ≤
      5 * family.secondBound / radius R j ^ 2 := by
  have hr := radius_pos hR j
  change |(scalarSub _ _).gradient k x| ≤ _
  rw [scalarSub_gradient]
  apply (abs_sub _ _).trans
  apply (add_le_add (family.second _ hr i k x)
    (family.second _ (radius_pos hR (j + 1)) i k x)).trans_eq
  rw [radius_succ]
  field_simp [hr.ne']
  ring

theorem derivatives_supported (family : BufferedFamily x₀) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (x : EuclideanSpace ℝ I)
    (hx : x ∉ ball x₀ (2 * radius R j) \ ball x₀ (radius R j / 2)) :
    (∀ i, (cutoff family R j).scalar.gradient i x = 0) ∧
      (∀ i k, ((cutoff family R j).derivative i).gradient k x = 0) := by
  have hr := radius_pos hR j
  have hrs := radius_pos hR (j + 1)
  have ho : x ∉ ball x₀ (2 * radius R j) \ ball x₀ (radius R j) := by
    intro h
    apply hx
    exact ⟨h.1, fun hh => h.2 (by
      change dist x x₀ < radius R j
      have hdist : dist x x₀ < radius R j / 2 := hh
      linarith)⟩
  have hi : x ∉ ball x₀ (2 * radius R (j + 1)) \ ball x₀ (radius R (j + 1)) := by
    rw [radius_succ]
    intro h
    apply hx
    exact ⟨by
      change dist x x₀ < 2 * radius R j
      have hdist : dist x x₀ < 2 * (radius R j / 2) := h.1
      linarith, h.2⟩
  have houter := buffered_derivatives_supported (family.cutoff _) hr (family.weight _ hr) x ho
  have hinner := buffered_derivatives_supported (family.cutoff _) hrs (family.weight _ hrs) x hi
  constructor
  · intro i
    change (scalarSub _ _).gradient i x = 0
    rw [scalarSub_gradient, houter.1 i, hinner.1 i, sub_zero]
  · intro i k
    change (scalarSub _ _).gradient k x = 0
    rw [scalarSub_gradient, houter.2 i k, hinner.2 i k, sub_zero]

/-- At any point only three dyadic difference cutoffs can be nonzero. -/
theorem overlap_card_le_three (family : BufferedFamily x₀) {R : ℝ} (hR : 0 < R)
    (S : Finset ℕ) (x : EuclideanSpace ℝ I) :
    (S.filter fun j => (cutoff family R j).scalar.weight x ≠ 0).card ≤ 3 := by
  classical
  let T := S.filter fun j => (cutoff family R j).scalar.weight x ≠ 0
  by_cases hT : T.Nonempty
  · let a := T.min' hT
    have ha : a ∈ T := Finset.min'_mem _ _
    have hwa := weight_supported family hR a x (Finset.mem_filter.mp ha).2
    have hsub : T ⊆ Finset.Icc a (a + 2) := by
      intro j hj
      have haj : a ≤ j := Finset.min'_le _ _ hj
      have hwj := weight_supported family hR j x (Finset.mem_filter.mp hj).2
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

/-- A larger cutoff equal to one on every nonzero dyadic difference.
It provides the auxiliary localization used by the first-order endpoint. -/
def enlarged (family : BufferedFamily x₀) (R : ℝ) (j : ℕ) : TwiceDifferentiableMultiplier I :=
  twiceSub (family.cutoff (2 * radius R j)) (family.cutoff (radius R j / 4))

theorem enlarged_weight_abs_le_one (family : BufferedFamily x₀) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (x : EuclideanSpace ℝ I) : |(enlarged family R j).scalar.weight x| ≤ 1 := by
  have hr := radius_pos hR j
  have ho := family_weight_bounds family (by positivity : 0 < 2 * radius R j) x
  have hi := family_weight_bounds family (by positivity : 0 < radius R j / 4) x
  change |(family.cutoff _).scalar.weight x - (family.cutoff _).scalar.weight x| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem enlarged_eq_one (family : BufferedFamily x₀) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (x : EuclideanSpace ℝ I)
    (hx : (cutoff family R j).scalar.weight x ≠ 0) :
    (enlarged family R j).scalar.weight x = 1 := by
  have hr := radius_pos hR j
  have hs := weight_supported family hR j x hx
  change (family.cutoff (2 * radius R j)).scalar.weight x -
    (family.cutoff (radius R j / 4)).scalar.weight x = 1
  rw [family.weight _ (by positivity), family.weight _ (by positivity),
    buffered_scaled_one (by positivity) (by linarith [hs.2]),
    buffered_scaled_zero (by positivity) (by linarith [hs.1])]
  norm_num

theorem enlarged_supported (family : BufferedFamily x₀) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (x : EuclideanSpace ℝ I)
    (hx : (enlarged family R j).scalar.weight x ≠ 0) :
    radius R j / 4 < dist x x₀ ∧ dist x x₀ < 4 * radius R j := by
  have hr := radius_pos hR j
  have heq : (enlarged family R j).scalar.weight x =
      scaled (bufferedBump I) x₀ (2 * radius R j) x -
        scaled (bufferedBump I) x₀ (radius R j / 4) x := by
    change (family.cutoff _).scalar.weight x - (family.cutoff _).scalar.weight x = _
    rw [family.weight _ (by positivity), family.weight _ (by positivity)]
  constructor
  · by_contra! hlo
    apply hx
    rw [heq, buffered_scaled_one (by positivity) (by linarith),
      buffered_scaled_one (by positivity) (by linarith)]
    simp
  · by_contra! hhi
    apply hx
    rw [heq, buffered_scaled_zero (by positivity) (by linarith),
      buffered_scaled_zero (by positivity) (by linarith)]
    simp

theorem enlarged_gradient_bound (family : BufferedFamily x₀) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (i : I) (x : EuclideanSpace ℝ I) :
    |(enlarged family R j).scalar.gradient i x| ≤
      (9 / 2 : ℝ) * family.firstBound / radius R j := by
  have hr := radius_pos hR j
  change |(scalarSub _ _).gradient i x| ≤ _
  rw [scalarSub_gradient]
  apply (abs_sub _ _).trans
  apply (add_le_add (family.first _ (by positivity) i x)
    (family.first _ (by positivity) i x)).trans_eq
  field_simp [hr.ne']
  ring

theorem enlarged_second_gradient_bound (family : BufferedFamily x₀) {R : ℝ} (hR : 0 < R)
    (j : ℕ) (i k : I) (x : EuclideanSpace ℝ I) :
    |((enlarged family R j).derivative i).gradient k x| ≤
      (65 / 4 : ℝ) * family.secondBound / radius R j ^ 2 := by
  have hr := radius_pos hR j
  change |(scalarSub _ _).gradient k x| ≤ _
  rw [scalarSub_gradient]
  apply (abs_sub _ _).trans
  apply (add_le_add (family.second _ (by positivity) i k x)
    (family.second _ (by positivity) i k x)).trans_eq
  field_simp [hr.ne']
  ring

theorem enlarged_overlap_card_le_five (family : BufferedFamily x₀) {R : ℝ} (hR : 0 < R)
    (S : Finset ℕ) (x : EuclideanSpace ℝ I) :
    (S.filter fun j => (enlarged family R j).scalar.weight x ≠ 0).card ≤ 5 := by
  classical
  let T := S.filter fun j => (enlarged family R j).scalar.weight x ≠ 0
  by_cases hT : T.Nonempty
  · let a := T.min' hT
    have ha : a ∈ T := Finset.min'_mem _ _
    have hwa := enlarged_supported family hR a x (Finset.mem_filter.mp ha).2
    have hsub : T ⊆ Finset.Icc a (a + 4) := by
      intro j hj
      have haj : a ≤ j := Finset.min'_le _ _ hj
      have hwj := enlarged_supported family hR j x (Finset.mem_filter.mp hj).2
      have hja : j < a + 5 := by
        by_contra! hja
        have hrj := radius_antitone hR.le hja
        rw [radius_add_five] at hrj
        linarith [radius_pos hR a]
      exact Finset.mem_Icc.mpr ⟨haj, by omega⟩
    exact (Finset.card_le_card hsub).trans_eq (by simp; omega)
  · have hz : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    change T.card ≤ 5
    rw [hz]
    simp

end PfHk.SmoothDyadicCutoffs
