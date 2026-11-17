import PfHk.SmoothCutoffGeometry
import PfHk.L2ScalarNorm
import PfHk.PhysicalLocalEnergyBallCutoff

/-! The annular support and pointwise convergence of the constructed
cutoffs for ordinary Hilbert-valued L2 fields. -/

noncomputable section
namespace PfHk.PhysicalCarlemanInput

open MeasureTheory Filter GptLean.ElectronicH1Space
open PfHk.PhysicalCutoffCommutator PfHk.SmoothCutoffBounds PfHk.PhysicalLocalEnergy
open scoped ENNReal Topology

set_option maxHeartbeats 20000
set_option Elab.async false

variable {I : Type} [Fintype I] [DecidableEq I]

def bufferedBallCutoff {x₀ : EuclideanSpace ℝ I} (a : BufferedFamily x₀) (r : ℝ) (hr : 0 < r) :
    BallCutoff x₀ r a.firstBound where
  multiplier := (a.cutoff r).scalar
  nonneg := by
    intro x
    rw [a.weight r hr]
    exact (bufferedBump I).nonneg
  le_one := by
    intro x
    rw [a.weight r hr]
    exact (bufferedBump I).le_one
  eq_one := by
    intro x hx
    rw [a.weight r hr]
    exact buffered_scaled_one hr (by have h : dist x x₀ < r := hx; linarith)
  eq_zero := by
    intro x hx
    rw [a.weight r hr]
    exact buffered_scaled_zero hr (by
      have h : 2 * r ≤ dist x x₀ := le_of_not_gt hx
      linarith)
  gradient_bound := a.first r hr

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem scalar_buffered_annular_support (u : L2 H I)
    {x₀ : EuclideanSpace ℝ I} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hεR : ε ≤ R / 4)
    (a b : TwiceDifferentiableMultiplier I)
    (ha : a.scalar.weight = scaled (bufferedBump I) x₀ (R / 2))
    (hb : b.scalar.weight = scaled (bufferedBump I) x₀ ε) :
    ∃ ρ R' : ℝ, 0 < ρ ∧ ρ < R' ∧ R' < R ∧
      ∀ᵐ x ∂volume, (dist x x₀ < ρ ∨ R' < dist x x₀) →
        (twiceSub a b).scalar.multiplier u x = 0 := by
  refine ⟨ε, 7 * R / 8, hε, by linarith, by linarith, ?_⟩
  filter_upwards [scalar_multiplier_ae (twiceSub a b).scalar u] with x hx
  intro hs
  have hweight : (twiceSub a b).scalar.weight x = 0 := by
    change a.scalar.weight x - b.scalar.weight x = 0
    rw [ha, hb]
    rcases hs with hi | ho
    · rw [buffered_scaled_one (half_pos hR) (by linarith),
        buffered_scaled_one hε (by linarith)]
      simp
    · rw [buffered_scaled_zero (half_pos hR) (by linarith),
        buffered_scaled_zero hε (by linarith)]
      simp
  rw [hx, hweight, zero_smul]

theorem scalar_buffered_cutoff_eventually_identity [Nonempty I] (u : L2 H I)
    {x₀ : EuclideanSpace ℝ I} {R inner : ℝ} (hR : 0 < R) (hi : inner ≤ R / 2)
    (a : TwiceDifferentiableMultiplier I) (b : ℕ → TwiceDifferentiableMultiplier I)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (ha : a.scalar.weight = scaled (bufferedBump I) x₀ (R / 2))
    (hb : ∀ n, (b n).scalar.weight = scaled (bufferedBump I) x₀ (ε n)) :
    ∀ᵐ x ∂volume.restrict (Metric.ball x₀ inner), ∀ᶠ n in atTop,
      (twiceSub a (b n)).scalar.multiplier u x =
        u x := by
  have hnot : ∀ᵐ x : EuclideanSpace ℝ I ∂volume, x ≠ x₀ := by
    simpa only [Set.mem_singleton_iff] using
      (measure_eq_zero_iff_ae_notMem.mp (measure_singleton x₀))
  have hfield : ∀ᵐ x ∂volume, ∀ n,
      (twiceSub a (b n)).scalar.multiplier u x =
        (twiceSub a (b n)).scalar.weight x • u x :=
    ae_all_iff.mpr fun n => scalar_multiplier_ae (twiceSub a (b n)).scalar u
  filter_upwards [ae_restrict_of_ae hnot, ae_restrict_of_ae hfield,
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hfx hball
  have hdist : 0 < dist x x₀ := dist_pos.mpr hx
  have hdouble : Tendsto (fun n => 2 * ε n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hεlim.const_mul 2
  have he : ∀ᶠ n in atTop, 2 * ε n < dist x x₀ :=
    hdouble.eventually (eventually_lt_nhds hdist)
  filter_upwards [he] with n hn
  have hoa : a.scalar.weight x = 1 := by
    rw [ha]
    exact buffered_scaled_one (half_pos hR) (by
      have hball' : dist x x₀ < inner := hball
      linarith)
  have hob : (b n).scalar.weight x = 0 := by
    rw [hb n]
    exact buffered_scaled_zero (hε n) (by linarith [hε n])
  rw [hfx n]
  change (a.scalar.weight x - (b n).scalar.weight x) • u x = _
  rw [hoa, hob, sub_zero, one_smul]

end PfHk.PhysicalCarlemanInput
