import PfHk.SmoothDyadicRegularity

/-! Scalar geometry for the enlarged annular cutoffs used in the
first-order perturbation estimate. -/

noncomputable section
namespace PfHk.SmoothDyadicCutoffs.Enlarged

open PfHk.SmoothDyadicCutoffs PfHk.SmoothCutoffBounds PfHk.PhysicalCutoffCommutator
  PfHk.CarlemanWeights Filter Metric
open scoped Topology

set_option Elab.async false
set_option maxHeartbeats 60000
attribute [local instance] Classical.propDecidable

theorem beta_annular_comparison {α r R : ℝ} (hα : 0 < α)
    (hαR : R ≤ Real.exp (-(4 * α + 2)))
    (hR : 0 < R) (hsmall : R ≤ Real.exp (-4)) (hlo : R / 4 ≤ r) (hhi : r ≤ 4 * R) :
    beta α (-Real.log R) ≤ 8 * beta α (-Real.log r) ∧
      beta α (-Real.log r) ≤ 8 * beta α (-Real.log R) := by
  have hr : 0 < r := by linarith
  have hαlog := alpha_threshold_of_radius hR hαR
  have hRlog : Real.log R ≤ -4 := by
    simpa only [Real.log_exp] using Real.log_le_log hR hsmall
  have hlogtwo : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    linarith
  have hlogfour : Real.log 4 < 2 := by
    have he : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
      norm_num
    rw [he]
    linarith
  have hupper := Real.log_le_log hr hhi
  have hlower := Real.log_le_log (show 0 < R / 4 by positivity) hlo
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hR.ne'] at hupper
  rw [Real.log_div hR.ne' (by norm_num : (4 : ℝ) ≠ 0)] at hlower
  have hrt : 0 < -Real.log r := by linarith
  have hRt : 0 < -Real.log R := by linarith
  exact ⟨beta_doubling hα hrt hRt (by linarith) (by linarith) (by linarith),
    beta_doubling hα hRt hrt (by linarith) (by linarith) (by linarith)⟩

variable {I : Type} [Fintype I] [DecidableEq I] {O : EuclideanSpace ℝ I}

def dyadicAnnulus (O : EuclideanSpace ℝ I) (R : ℝ) (j : ℕ) : Set (EuclideanSpace ℝ I) :=
  {x | radius R j / 4 ≤ dist x O ∧ dist x O ≤ 4 * radius R j}

theorem dyadicAnnulus_measurable (O : EuclideanSpace ℝ I) (R : ℝ) (j : ℕ) :
    MeasurableSet (dyadicAnnulus O R j) := by
  exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet.inter
    (isClosed_le (continuous_id.dist continuous_const) continuous_const).measurableSet

theorem annulus_overlap_card_le_five (O : EuclideanSpace ℝ I) {R : ℝ} (hR : 0 < R)
    (S : Finset ℕ) (x : EuclideanSpace ℝ I) :
    (S.filter fun j => x ∈ dyadicAnnulus O R j).card ≤ 5 := by
  classical
  let T := S.filter fun j => x ∈ dyadicAnnulus O R j
  by_cases hT : T.Nonempty
  · let a := T.min' hT
    have ha : a ∈ T := Finset.min'_mem _ _
    have hwa : radius R a / 4 ≤ dist x O ∧ dist x O ≤ 4 * radius R a :=
      (Finset.mem_filter.mp ha).2
    have hsub : T ⊆ Finset.Icc a (a + 4) := by
      intro j hj
      have haj : a ≤ j := Finset.min'_le _ _ hj
      have hwj : radius R j / 4 ≤ dist x O ∧ dist x O ≤ 4 * radius R j :=
        (Finset.mem_filter.mp hj).2
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

theorem sum_le_five_of_annular_bound (O : EuclideanSpace ℝ I) {R : ℝ} (hR : 0 < R)
    (S : Finset ℕ) (x : EuclideanSpace ℝ I) (v : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ j ∈ S, x ∉ dyadicAnnulus O R j → v j = 0)
    (hbound : ∀ j ∈ S, x ∈ dyadicAnnulus O R j → v j ≤ B) :
    (∑ j ∈ S, v j) ≤ 5 * B := by
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
    _ ≤ 5 * B := mul_le_mul_of_nonneg_right
      (by exact_mod_cast annulus_overlap_card_le_five O hR S x) hB

theorem cutoff_contDiff (family : BufferedFamily O) {R : ℝ} (hR : 0 < R) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (enlarged family R j).scalar.weight := by
  have hrj := radius_pos hR j
  have hb (r : ℝ) (hr : 0 < r) :
      ContDiff ℝ (⊤ : ℕ∞) (family.cutoff r).scalar.weight := by
    rw [family.weight r hr]
    exact (bufferedBump I).contDiff.comp
      (ContDiff.const_smul r⁻¹ (contDiff_id.sub contDiff_const))
  exact (hb _ (by positivity : 0 < 2 * radius R j)).sub
    (hb _ (by positivity : 0 < radius R j / 4))

theorem cutoff_hasCompactSupport (family : BufferedFamily O) {R : ℝ} (hR : 0 < R) (j : ℕ) :
    HasCompactSupport (enlarged family R j).scalar.weight := by
  apply (isCompact_closedBall O (4 * radius R j)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  exact (enlarged_supported family hR j x hx).2.le

theorem cutoff_eventually_zero (family : BufferedFamily O) {R : ℝ} (hR : 0 < R) (j : ℕ)
    {x : EuclideanSpace ℝ I} (hx : x ∉ dyadicAnnulus O R j) :
    (enlarged family R j).scalar.weight =ᶠ[𝓝 x] fun _ => 0 := by
  have hopen : IsOpen ((dyadicAnnulus O R j)ᶜ) := by
    exact ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)).isOpen_compl
  filter_upwards [hopen.mem_nhds hx] with y hy
  by_contra hn
  have hsupport := enlarged_supported family hR j y hn
  exact hy ⟨hsupport.1.le, hsupport.2.le⟩

theorem cutoff_eventually_zero_center (family : BufferedFamily O) {R : ℝ} (hR : 0 < R)
    (j : ℕ) : (enlarged family R j).scalar.weight =ᶠ[𝓝 O] fun _ => 0 := by
  apply cutoff_eventually_zero family hR j
  intro h
  have hlo : radius R j / 4 ≤ dist O O := h.1
  simp only [dist_self] at hlo
  linarith [radius_pos hR j]

end PfHk.SmoothDyadicCutoffs.Enlarged
