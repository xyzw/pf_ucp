import PfHk.SmoothDyadicRegularity
import PfHk.SpatialCarlemanWeight

/-! Actual compact smooth annular exponential multipliers. The
exponential stays at its spatial argument in every derivative bound. -/

noncomputable section
namespace PfHk.SmoothDyadicCutoffs

open PfHk.SmoothCutoffBounds PfHk.PhysicalCutoffCommutator PfHk.SpatialCarlemanWeight
  PfHk.CarlemanWeights GptLean.ElectronicH1Multiplier Filter Metric
open scoped Topology

set_option Elab.async false
set_option maxHeartbeats 100000

variable {I : Type} [Fintype I] [DecidableEq I] {O : EuclideanSpace ℝ I}

def weightedFunction (family : BufferedFamily O) (R τ α : ℝ) (j : ℕ)
    (x : EuclideanSpace ℝ I) : ℝ :=
  (cutoff family R j).scalar.weight x * spatialExp τ α O x

theorem weightedFunction_contDiff (family : BufferedFamily O) {R : ℝ} (hR : 0 < R)
    (τ α : ℝ) (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (weightedFunction family R τ α j) :=
  smooth_product_off_point _ _ O (cutoff_contDiff family hR j)
    (spatialExp_contDiffAt τ α O) (cutoff_eventually_zero_center family hR j)

theorem weightedFunction_hasCompactSupport (family : BufferedFamily O) {R : ℝ}
    (hR : 0 < R) (τ α : ℝ) (j : ℕ) :
    HasCompactSupport (weightedFunction family R τ α j) :=
  (cutoff_hasCompactSupport family hR j).mul_right

def weightedCutoff (family : BufferedFamily O) (R : ℝ) (hR : 0 < R) (τ α : ℝ) (j : ℕ) :
    TwiceDifferentiableMultiplier I :=
  compactMultiplier (weightedFunction family R τ α j)
    (weightedFunction_contDiff family hR τ α j)
    (weightedFunction_hasCompactSupport family hR τ α j)

theorem weightedCutoff_weight (family : BufferedFamily O) {R : ℝ} (hR : 0 < R)
    (τ α : ℝ) (j : ℕ) :
    (weightedCutoff family R hR τ α j).scalar.weight = weightedFunction family R τ α j :=
  compactMultiplier_weight _ _ _

theorem weightedCutoff_gradient (family : BufferedFamily O) {R : ℝ} (hR : 0 < R)
    (τ α : ℝ) (j : ℕ) (i : I) (x : EuclideanSpace ℝ I) :
    (weightedCutoff family R hR τ α j).scalar.gradient i x =
      coordinateDerivative (weightedFunction family R τ α j) i x :=
  compactMultiplier_gradient _ _ _ _ _

theorem weightedCutoff_second (family : BufferedFamily O) {R : ℝ} (hR : 0 < R)
    (τ α : ℝ) (j : ℕ) (i k : I) (x : EuclideanSpace ℝ I) :
    ((weightedCutoff family R hR τ α j).derivative i).gradient k x =
      coordinateDerivative (coordinateDerivative (weightedFunction family R τ α j) i) k x :=
  compactMultiplier_second _ _ _ _ _ _

theorem weightedCutoff_supported (family : BufferedFamily O) {R : ℝ} (hR : 0 < R)
    (τ α : ℝ) (j : ℕ) (x : EuclideanSpace ℝ I) (hx : x ∉ dyadicAnnulus O R j) :
    (weightedCutoff family R hR τ α j).scalar.weight x = 0 ∧
      (∀ i, (weightedCutoff family R hR τ α j).scalar.gradient i x = 0) ∧
      (∀ i k, ((weightedCutoff family R hR τ α j).derivative i).gradient k x = 0) := by
  have hz : (weightedCutoff family R hR τ α j).scalar.weight =ᶠ[𝓝 x] fun _ => 0 := by
    rw [weightedCutoff_weight]
    filter_upwards [cutoff_eventually_zero family hR j hx] with y hy
    change (cutoff family R j).scalar.weight y * spatialExp τ α O y = 0
    rw [hy, zero_mul]
  exact ⟨hz.eq_of_nhds, fun i => gradient_eq_zero_of_eventually_constant _ hz i,
    fun i k => second_gradient_eq_zero_of_eventually_constant _ hz i k⟩

theorem annulus_log_bound {R : ℝ} (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2))
    (j : ℕ) {x : EuclideanSpace ℝ I} (hx : x ∈ dyadicAnnulus O R j) :
    x ≠ O ∧ 2 ≤ -Real.log (dist x O) := by
  have hrj := radius_pos hR j
  have hr : 0 < dist x O := by have h := hx.1; linarith
  have hrjR : radius R j ≤ R := by
    simpa only [radius, pow_zero, div_one] using radius_antitone hR.le (Nat.zero_le j)
  have hxr : dist x O ≤ Real.exp (-2) := by have h := hx.2; linarith
  have hlog := Real.log_le_log hr hxr
  rw [Real.log_exp] at hlog
  exact ⟨dist_pos.mp hr, by linarith⟩

theorem weightedCutoff_weight_bound (family : BufferedFamily O) {R : ℝ} (hR : 0 < R)
    (hsmall : 2 * R ≤ Real.exp (-2)) (τ α : ℝ) (j : ℕ) (x : EuclideanSpace ℝ I)
    (hx : x ∈ dyadicAnnulus O R j) :
    |(weightedCutoff family R hR τ α j).scalar.weight x| ≤
      Real.exp (τ * weight α (-Real.log (dist x O))) := by
  rw [weightedCutoff_weight, weightedFunction, spatialExp_eq τ α O x
    (by linarith [(annulus_log_bound hR hsmall j hx).2]), abs_mul,
      abs_of_pos (Real.exp_pos _)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (weight_abs_le_one family hR j x) (Real.exp_pos _).le

/-- The compact smooth realization agrees everywhere with the literal
annular cutoff times the physical exponential weight. -/
theorem weightedCutoff_actual_weight (family : BufferedFamily O) {R : ℝ} (hR : 0 < R)
    (hsmall : 2 * R ≤ Real.exp (-2)) (τ α : ℝ) (j : ℕ) (x : EuclideanSpace ℝ I) :
    (weightedCutoff family R hR τ α j).scalar.weight x =
      (cutoff family R j).scalar.weight x * Real.exp (τ * weight α (-Real.log (dist x O))) := by
  by_cases hx : x ∈ dyadicAnnulus O R j
  · rw [weightedCutoff_weight, weightedFunction, spatialExp_eq τ α O x
      (by linarith [(annulus_log_bound hR hsmall j hx).2])]
  · rw [(weightedCutoff_supported family hR τ α j x hx).1]
    have hη : (cutoff family R j).scalar.weight x = 0 := by
      by_contra hn
      have h := weight_supported family hR j x hn
      exact hx ⟨h.1.le, h.2.le⟩
    rw [hη, zero_mul]

def firstWeightConstant (family : BufferedFamily O) : ℝ := 3 * family.firstBound + 2
def secondWeightConstant (family : BufferedFamily O) : ℝ :=
  5 * family.secondBound + 12 * family.firstBound + 20

theorem firstWeightConstant_nonneg (family : BufferedFamily O) : 0 ≤ firstWeightConstant family := by
  unfold firstWeightConstant
  linarith [family.first_nonneg]

theorem secondWeightConstant_nonneg (family : BufferedFamily O) : 0 ≤ secondWeightConstant family := by
  unfold secondWeightConstant
  linarith [family.first_nonneg, family.second_nonneg]

private theorem inverse_annular_bounds {r q : ℝ} (hq : 0 < q) (hlo : q / 2 ≤ r) :
    1 / r ≤ 2 / q ∧ 1 / r ^ 2 ≤ 4 / q ^ 2 := by
  have hr : 0 < r := by linarith
  have hfirst : 1 / r ≤ 2 / q := (div_le_div_iff₀ hr hq).mpr (by linarith)
  refine ⟨hfirst, ?_⟩
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / r) hfirst 2
  simpa only [div_pow, one_pow, show (2 : ℝ)^2 = 4 by norm_num] using h

theorem weightedCutoff_first_bound (family : BufferedFamily O) {R τ α : ℝ} (hR : 0 < R)
    (hsmall : 2 * R ≤ Real.exp (-2)) (hτ : 1 ≤ τ) (hα : 0 < α)
    (j : ℕ) (x : EuclideanSpace ℝ I) (hx : x ∈ dyadicAnnulus O R j) (i : I) :
    |(weightedCutoff family R hR τ α j).scalar.gradient i x| ≤
      firstWeightConstant family * τ / radius R j *
        Real.exp (τ * weight α (-Real.log (dist x O))) := by
  obtain ⟨hne, ht⟩ := annulus_log_bound hR hsmall j hx
  have hrj := radius_pos hR j
  have hτ0 : 0 ≤ τ := by linarith
  have hE := (Real.exp_pos (τ * weight α (-Real.log (dist x O)))).le
  have he := spatialExp_eq τ α O x (by linarith : 1 ≤ -Real.log (dist x O))
  have hde : |coordinateDerivative (spatialExp τ α O) i x| ≤
      2 * τ / radius R j * Real.exp (τ * weight α (-Real.log (dist x O))) := by
    apply (spatialExp_first_bound hτ hα O x hne ht i).trans
    have hi := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (inverse_annular_bounds hrj hx.1).1 hτ0) hE
    convert hi using 1 <;> ring
  rw [weightedCutoff_gradient]
  change |coordinateDerivative (fun y => (cutoff family R j).scalar.weight y *
    spatialExp τ α O y) i x| ≤ _
  rw [coordinateDerivative_mul_at _ _ i
    ((cutoff_contDiff family hR j).differentiable (by simp) x)
    ((spatialExp_contDiffAt τ α O x hne).differentiableAt (by simp))]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, he, abs_of_nonneg hE]
  have hη := weight_abs_le_one family hR j x
  have hdη : |coordinateDerivative (cutoff family R j).scalar.weight i x| ≤
      3 * family.firstBound / radius R j := gradient_bound family hR j i x
  apply (add_le_add
    (mul_le_mul hη hde (abs_nonneg _) zero_le_one)
    (mul_le_mul_of_nonneg_left hdη hE)).trans
  have hb : 3 * family.firstBound ≤ 3 * family.firstBound * τ := by
    nlinarith [mul_nonneg family.first_nonneg (show 0 ≤ τ - 1 by linarith)]
  have h := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hrj.le) hE
  unfold firstWeightConstant
  calc
    _ = 2 * τ / radius R j * Real.exp (τ * weight α (-Real.log (dist x O))) +
        3 * family.firstBound / radius R j * Real.exp (τ * weight α (-Real.log (dist x O))) := by ring
    _ ≤ 2 * τ / radius R j * Real.exp (τ * weight α (-Real.log (dist x O))) +
        3 * family.firstBound * τ / radius R j * Real.exp (τ * weight α (-Real.log (dist x O))) :=
      add_le_add le_rfl h
    _ = _ := by ring

theorem weightedCutoff_second_bound (family : BufferedFamily O) {R τ α : ℝ} (hR : 0 < R)
    (hsmall : 2 * R ≤ Real.exp (-2)) (hτ : 1 ≤ τ) (hα : 0 < α)
    (j : ℕ) (x : EuclideanSpace ℝ I) (hx : x ∈ dyadicAnnulus O R j) (i k : I) :
    |((weightedCutoff family R hR τ α j).derivative i).gradient k x| ≤
      secondWeightConstant family * τ^2 / (radius R j)^2 *
        Real.exp (τ * weight α (-Real.log (dist x O))) := by
  obtain ⟨hne, ht⟩ := annulus_log_bound hR hsmall j hx
  have hrj := radius_pos hR j
  have hτ0 : 0 ≤ τ := by linarith
  let E := Real.exp (τ * weight α (-Real.log (dist x O)))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have he : spatialExp τ α O x = E := spatialExp_eq τ α O x (by linarith)
  have hde (l : I) : |coordinateDerivative (spatialExp τ α O) l x| ≤
      2 * τ / radius R j * E := by
    apply (spatialExp_first_bound hτ hα O x hne ht l).trans
    have hi := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (inverse_annular_bounds hrj hx.1).1 hτ0) hE
    convert hi using 1 <;> ring
  have hdde : |coordinateDerivative (coordinateDerivative (spatialExp τ α O) i) k x| ≤
      20 * τ^2 / (radius R j)^2 * E := by
    apply (spatialExp_second_bound hτ hα O x hne ht i k).trans
    have hi := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (inverse_annular_bounds hrj hx.1).2
        (by positivity : 0 ≤ 5 * τ^2)) hE
    convert hi using 1 <;> ring
  have hdη (l : I) : |coordinateDerivative (cutoff family R j).scalar.weight l x| ≤
      3 * family.firstBound / radius R j := gradient_bound family hR j l x
  have hddη : |coordinateDerivative (coordinateDerivative (cutoff family R j).scalar.weight i) k x| ≤
      5 * family.secondBound / (radius R j)^2 := by
    have h := second_gradient_bound family hR j i k x
    change |coordinateDerivative ((cutoff family R j).derivative i).weight k x| ≤ _ at h
    rw [(cutoff family R j).derivative_weight] at h
    exact h
  rw [weightedCutoff_second]
  change |coordinateDerivative (coordinateDerivative (fun y =>
    (cutoff family R j).scalar.weight y * spatialExp τ α O y) i) k x| ≤ _
  rw [coordinateDerivative_second_mul _ _ i k
    ((cutoff_contDiff family hR j).contDiffAt.of_le (by simp))
    ((spatialExp_contDiffAt τ α O x hne).of_le (by simp))]
  have hab := abs_add_le
    ((cutoff family R j).scalar.weight x * coordinateDerivative (coordinateDerivative (spatialExp τ α O) i) k x +
      coordinateDerivative (cutoff family R j).scalar.weight k x * coordinateDerivative (spatialExp τ α O) i x +
      spatialExp τ α O x * coordinateDerivative (coordinateDerivative (cutoff family R j).scalar.weight i) k x)
    (coordinateDerivative (spatialExp τ α O) k x * coordinateDerivative (cutoff family R j).scalar.weight i x)
  apply hab.trans
  apply (add_le_add (abs_add_le _ _) le_rfl).trans
  apply (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl).trans
  rw [abs_mul, abs_mul, abs_mul, abs_mul, he, abs_of_nonneg hE]
  have h₁ := mul_le_mul (weight_abs_le_one family hR j x) hdde (abs_nonneg _) zero_le_one
  have h₂ := mul_le_mul (hdη k) (hde i) (abs_nonneg _)
    (div_nonneg (mul_nonneg (by norm_num) family.first_nonneg) hrj.le)
  have h₃ := mul_le_mul_of_nonneg_left hddη hE
  have h₄ := mul_le_mul (hde k) (hdη i) (abs_nonneg _) (by positivity)
  apply (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄).trans
  have hb : 20 * τ^2 + 12 * family.firstBound * τ + 5 * family.secondBound ≤
      secondWeightConstant family * τ^2 := by
    unfold secondWeightConstant
    nlinarith [mul_nonneg family.first_nonneg (show 0 ≤ τ^2 - τ by nlinarith),
      mul_nonneg family.second_nonneg (show 0 ≤ τ^2 - 1 by nlinarith)]
  have h := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hb (sq_nonneg (radius R j))) hE
  convert h using 1 <;> ring

/-- Annularly supported vectors meet only finitely many members of the
actual weighted dyadic family. -/
theorem weightedCutoff_eventually_zero_outside (family : BufferedFamily O)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (τ α : ℝ) :
    ∃ J : ℕ, ∀ j, J ≤ j → ∀ x : EuclideanSpace ℝ I, ρ ≤ dist x O →
      (weightedCutoff family R hR τ α j).scalar.weight x = 0 := by
  obtain ⟨J, hJ⟩ := exists_inner_radius (R := R) hρ
  refine ⟨J, ?_⟩
  intro j hj x hx
  rw [weightedCutoff_weight, weightedFunction]
  have hzero : (cutoff family R j).scalar.weight x = 0 := by
    by_contra hn
    have h := (weight_supported family hR j x hn).2
    have hm := radius_antitone hR.le hj
    linarith
  rw [hzero, zero_mul]

end PfHk.SmoothDyadicCutoffs
