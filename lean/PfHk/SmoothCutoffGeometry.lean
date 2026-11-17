import PfHk.SmoothCutoffBounds
import PfHk.SmoothCutoffOperations

/-! Scalar support and derivative support of the constructed smooth
cutoffs. The transition has a margin on both sides of its annulus. -/

noncomputable section
namespace PfHk.SmoothCutoffBounds

open Filter Metric GptLean GptLean.ElectronicH1Multiplier
open PfHk.PhysicalCutoffCommutator
open scoped Topology

set_option maxHeartbeats 20000
set_option Elab.async false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- One scalar family at all radii, with constants independent of the
center and radius. All fields describe ordinary real functions. -/
structure BufferedFamily (x₀ : EuclideanSpace ℝ I) where
  firstBound : ℝ
  secondBound : ℝ
  first_nonneg : 0 ≤ firstBound
  second_nonneg : 0 ≤ secondBound
  cutoff : ℝ → TwiceDifferentiableMultiplier I
  weight : ∀ r, 0 < r → (cutoff r).scalar.weight = scaled (bufferedBump I) x₀ r
  first : ∀ r, 0 < r → ∀ i x, |(cutoff r).scalar.gradient i x| ≤ firstBound / r
  second : ∀ r, 0 < r → ∀ i j x, |((cutoff r).derivative i).gradient j x| ≤ secondBound / r ^ 2

theorem exists_buffered_family (x₀ : EuclideanSpace ℝ I) : Nonempty (BufferedFamily x₀) := by
  classical
  obtain ⟨B₁, B₂, hB₁, hB₂, hfamily⟩ := exists_buffered_twice I
  choose a ha hfirst hsecond using fun r hr => hfamily x₀ r hr
  let c := fun r => if hr : 0 < r then a r hr else a 1 zero_lt_one
  refine ⟨⟨B₁, B₂, hB₁, hB₂, c, ?_, ?_, ?_⟩⟩
  · intro r hr
    simpa only [c, dite_eq_left hr] using ha r hr
  · intro r hr
    simpa only [c, dite_eq_left hr] using hfirst r hr
  · intro r hr
    simpa only [c, dite_eq_left hr] using hsecond r hr

theorem gradient_eq_zero_of_eventually_constant (a : DifferentiableMultiplier I)
    {x : EuclideanSpace ℝ I} {c : ℝ}
    (h : a.weight =ᶠ[𝓝 x] fun _ => c) (i : I) : a.gradient i x = 0 := by
  unfold DifferentiableMultiplier.gradient
  rw [h.fderiv_eq]
  simp

theorem second_gradient_eq_zero_of_eventually_constant (a : TwiceDifferentiableMultiplier I)
    {x : EuclideanSpace ℝ I} {c : ℝ}
    (h : a.scalar.weight =ᶠ[𝓝 x] fun _ => c) (i j : I) :
    (a.derivative i).gradient j x = 0 := by
  apply gradient_eq_zero_of_eventually_constant
  have hg : a.scalar.gradient i =ᶠ[𝓝 x] fun _ => 0 :=
    h.eventuallyEq_nhds.mono fun y hy => gradient_eq_zero_of_eventually_constant a.scalar hy i
  simpa only [a.derivative_weight i] using hg

theorem scaled_dist {x x₀ : EuclideanSpace ℝ I} {r : ℝ} (hr : 0 < r) :
    dist (r⁻¹ • (x - x₀)) 0 = dist x x₀ / r := by
  simp only [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hr, div_eq_mul_inv, mul_comm]

theorem buffered_scaled_one {x x₀ : EuclideanSpace ℝ I} {r : ℝ} (hr : 0 < r)
    (hx : dist x x₀ ≤ 5 * r / 4) : scaled (bufferedBump I) x₀ r x = 1 := by
  apply (bufferedBump I).one_of_mem_closedBall
  change dist (r⁻¹ • (x - x₀)) 0 ≤ 5 / 4
  rw [scaled_dist hr]
  apply (div_le_iff₀ hr).mpr
  linarith

theorem buffered_scaled_zero {x x₀ : EuclideanSpace ℝ I} {r : ℝ} (hr : 0 < r)
    (hx : 7 * r / 4 ≤ dist x x₀) : scaled (bufferedBump I) x₀ r x = 0 := by
  apply (bufferedBump I).zero_of_le_dist
  change 7 / 4 ≤ dist (r⁻¹ • (x - x₀)) 0
  rw [scaled_dist hr]
  apply (le_div_iff₀ hr).mpr
  linarith

theorem buffered_scaled_eventually_one {x x₀ : EuclideanSpace ℝ I} {r : ℝ}
    (hr : 0 < r) (hx : dist x x₀ ≤ r) :
    scaled (bufferedBump I) x₀ r =ᶠ[𝓝 x] fun _ => 1 := by
  have he : ∀ᶠ y in 𝓝 x, dist y x₀ < 5 * r / 4 :=
    (continuous_id.dist continuous_const).continuousAt.eventually_lt_const
      (by change dist x x₀ < 5 * r / 4; linarith)
  exact he.mono fun y hy => buffered_scaled_one hr hy.le

theorem buffered_scaled_eventually_zero {x x₀ : EuclideanSpace ℝ I} {r : ℝ}
    (hr : 0 < r) (hx : 2 * r ≤ dist x x₀) :
    scaled (bufferedBump I) x₀ r =ᶠ[𝓝 x] fun _ => 0 := by
  have he : ∀ᶠ y in 𝓝 x, 7 * r / 4 < dist y x₀ :=
    (continuous_id.dist continuous_const).continuousAt.eventually_const_lt
      (by change 7 * r / 4 < dist x x₀; linarith)
  exact he.mono fun y hy => buffered_scaled_zero hr hy.le

/-- Both orders of derivatives vanish outside the scalar transition annulus. -/
theorem buffered_derivatives_supported (a : TwiceDifferentiableMultiplier I)
    {x₀ : EuclideanSpace ℝ I} {r : ℝ} (hr : 0 < r)
    (ha : a.scalar.weight = scaled (bufferedBump I) x₀ r)
    (x : EuclideanSpace ℝ I) (hx : x ∉ ball x₀ (2 * r) \ ball x₀ r) :
    (∀ i, a.scalar.gradient i x = 0) ∧
      ∀ i j, (a.derivative i).gradient j x = 0 := by
  by_cases hi : dist x x₀ < r
  · have h := buffered_scaled_eventually_one hr hi.le
    rw [← ha] at h
    exact ⟨fun i => gradient_eq_zero_of_eventually_constant a.scalar h i,
      fun i j => second_gradient_eq_zero_of_eventually_constant a h i j⟩
  · have ho : 2 * r ≤ dist x x₀ := by
      by_contra! ho
      exact hx ⟨ho, hi⟩
    have h := buffered_scaled_eventually_zero hr ho
    rw [← ha] at h
    exact ⟨fun i => gradient_eq_zero_of_eventually_constant a.scalar h i,
      fun i j => second_gradient_eq_zero_of_eventually_constant a h i j⟩

theorem sum_gradient_sq_bound (a : TwiceDifferentiableMultiplier I)
    {B r : ℝ} (_hB : 0 ≤ B) (_hr : 0 < r)
    (hbound : ∀ i x, |a.scalar.gradient i x| ≤ B / r) (x : EuclideanSpace ℝ I) :
    (∑ i, a.scalar.gradient i x ^ 2) ≤ (Fintype.card I : ℝ) * B ^ 2 / r ^ 2 := by
  calc
    _ ≤ ∑ _ : I, (B / r) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using pow_le_pow_left₀
        (abs_nonneg (a.scalar.gradient i x)) (hbound i x) 2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem sum_second_gradient_sq_bound (a : TwiceDifferentiableMultiplier I)
    {B r : ℝ} (_hB : 0 ≤ B) (_hr : 0 < r)
    (hbound : ∀ i j x, |(a.derivative i).gradient j x| ≤ B / r ^ 2)
    (x : EuclideanSpace ℝ I) :
    (∑ i, (a.derivative i).gradient i x) ^ 2 ≤
      ((Fintype.card I : ℝ) * B) ^ 2 / r ^ 4 := by
  have habs : |∑ i, (a.derivative i).gradient i x| ≤ (Fintype.card I : ℝ) * (B / r ^ 2) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i i x))
  calc
    _ ≤ ((Fintype.card I : ℝ) * (B / r ^ 2)) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀
        (abs_nonneg (∑ i, (a.derivative i).gradient i x)) habs 2
    _ = _ := by ring
end PfHk.SmoothCutoffBounds
