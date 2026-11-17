import PfHk.DyadicWeightGeometry
import PfHk.SmoothCompactMultiplier

noncomputable section
namespace PfHk.SmoothDyadicCutoffs

open PfHk.SmoothCutoffBounds PfHk.PhysicalCutoffCommutator Filter Metric
open scoped Topology

set_option Elab.async false
set_option maxHeartbeats 50000
variable {I : Type} [Fintype I] [DecidableEq I] {O : EuclideanSpace ℝ I}

/-- The derivative constants come from a single bump, before its center
is chosen. This makes every later annular constant uniform in the center. -/
theorem exists_uniform_buffered_family :
    ∃ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧
      ∀ O : EuclideanSpace ℝ I, ∃ family : BufferedFamily O,
        family.firstBound = B₁ ∧ family.secondBound = B₂ := by
  classical
  obtain ⟨B₁, B₂, hB₁, hB₂, hfamily⟩ := exists_buffered_twice I
  refine ⟨B₁, B₂, hB₁, hB₂, ?_⟩
  intro O
  choose a ha hfirst hsecond using fun r hr => hfamily O r hr
  let c := fun r => if hr : 0 < r then a r hr else a 1 zero_lt_one
  have hc : ∀ r, 0 < r → (c r).scalar.weight = scaled (bufferedBump I) O r := by
    intro r hr
    simpa only [c, dite_eq_left hr] using ha r hr
  have hcf : ∀ r, 0 < r → ∀ i x, |(c r).scalar.gradient i x| ≤ B₁ / r := by
    intro r hr
    simpa only [c, dite_eq_left hr] using hfirst r hr
  have hcs : ∀ r, 0 < r → ∀ i j x, |((c r).derivative i).gradient j x| ≤ B₂ / r^2 := by
    intro r hr
    simpa only [c, dite_eq_left hr] using hsecond r hr
  exact ⟨⟨B₁, B₂, hB₁, hB₂, c, hc, hcf, hcs⟩, rfl, rfl⟩

theorem cutoff_contDiff (family : BufferedFamily O) {R : ℝ} (hR : 0 < R) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoff family R j).scalar.weight := by
  have hb (r : ℝ) (hr : 0 < r) :
      ContDiff ℝ (⊤ : ℕ∞) (family.cutoff r).scalar.weight := by
    rw [family.weight r hr]
    exact (bufferedBump I).contDiff.comp
      (ContDiff.const_smul r⁻¹ (contDiff_id.sub contDiff_const))
  exact (hb _ (radius_pos hR j)).sub (hb _ (radius_pos hR (j + 1)))

theorem cutoff_hasCompactSupport (family : BufferedFamily O) {R : ℝ} (hR : 0 < R) (j : ℕ) :
    HasCompactSupport (cutoff family R j).scalar.weight := by
  apply (isCompact_closedBall O (2 * radius R j)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  exact (weight_supported family hR j x hx).2.le

theorem cutoff_eventually_zero (family : BufferedFamily O) {R : ℝ} (hR : 0 < R) (j : ℕ)
    {x : EuclideanSpace ℝ I} (hx : x ∉ dyadicAnnulus O R j) :
    (cutoff family R j).scalar.weight =ᶠ[𝓝 x] fun _ => 0 := by
  have hopen : IsOpen ((dyadicAnnulus O R j)ᶜ) := by
    exact ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)).isOpen_compl
  filter_upwards [hopen.mem_nhds hx] with y hy
  by_contra hn
  have hsupport := weight_supported family hR j y hn
  exact hy ⟨hsupport.1.le, hsupport.2.le⟩

theorem cutoff_eventually_zero_center (family : BufferedFamily O) {R : ℝ} (hR : 0 < R)
    (j : ℕ) : (cutoff family R j).scalar.weight =ᶠ[𝓝 O] fun _ => 0 := by
  apply cutoff_eventually_zero family hR j
  intro h
  have hlo : radius R j / 2 ≤ dist O O := h.1
  simp only [dist_self] at hlo
  linarith [radius_pos hR j]

end PfHk.SmoothDyadicCutoffs
