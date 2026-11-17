import PfHk.PhysicalCarlemanInput
import PfHk.CarlemanAnnularWeights

/-! A compact annular support has an open annular neighborhood strictly
inside the requested ball. All radii are chosen from the support witness. -/

noncomputable section
namespace PfHk.AnnularSupportGeometry

open MeasureTheory Set GptLean.PhysicalPFReference PfHk.PhysicalCarlemanInput
  PfHk.CarlemanSpatialDensity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

variable {I : Type} [Fintype I] [DecidableEq I]

def buffer (ρ R r₀ : ℝ) : Set (Position I) :=
  {x | ρ / 2 < ‖x‖ ∧ ‖x‖ < (R + r₀) / 2}

theorem buffer_open (ρ R r₀ : ℝ) : IsOpen (buffer (I := I) ρ R r₀) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem annulus_subset_buffer {ρ R r₀ : ℝ} (hρ : 0 < ρ) (hR : R < r₀) :
    annulus (I := I) ρ R ⊆ buffer ρ R r₀ := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := annulus_norm hx
  exact ⟨by linarith, by linarith⟩

theorem buffer_subset_annulus (ρ R r₀ : ℝ) :
    buffer (I := I) ρ R r₀ ⊆ annulus (ρ / 2) ((R + r₀) / 2) := by
  intro x hx
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2.le,
    by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx.1.le⟩

theorem buffer_positive {ρ R r₀ : ℝ} (hρ : 0 < ρ) :
    ∀ x ∈ buffer (I := I) ρ R r₀, 0 < ‖x‖ := by
  intro x hx
  exact (half_pos hρ).trans hx.1

theorem buffer_subset_ball {ρ R r₀ : ℝ} (hR : R < r₀) :
    buffer (I := I) ρ R r₀ ⊆ Metric.ball 0 r₀ := by
  intro x hx
  simp only [Metric.mem_ball, dist_zero_right]
  exact hx.2.trans (by linarith)

def innerRadius (ψ : WaveSpace I) (r₀ : ℝ) (h : AnnularSupport ψ 0 r₀) : ℝ :=
  Classical.choose h

def outerRadius (ψ : WaveSpace I) (r₀ : ℝ) (h : AnnularSupport ψ 0 r₀) : ℝ :=
  Classical.choose (Classical.choose_spec h)

theorem radii_spec (ψ : WaveSpace I) (r₀ : ℝ) (h : AnnularSupport ψ 0 r₀) :
    0 < innerRadius ψ r₀ h ∧ innerRadius ψ r₀ h < outerRadius ψ r₀ h ∧
      outerRadius ψ r₀ h < r₀ ∧
      ∀ᵐ x ∂volume, (‖x‖ < innerRadius ψ r₀ h ∨ outerRadius ψ r₀ h < ‖x‖) → ψ x = 0 := by
  simpa only [innerRadius, outerRadius, dist_zero_right] using
    Classical.choose_spec (Classical.choose_spec h)

theorem supported_annulus (ψ : WaveSpace I) (r₀ : ℝ) (h : AnnularSupport ψ 0 r₀) :
    ∀ᵐ x ∂volume, x ∉ annulus (innerRadius ψ r₀ h) (outerRadius ψ r₀ h) → ψ x = 0 := by
  filter_upwards [(radii_spec ψ r₀ h).2.2.2] with x hx hxs
  apply hx
  by_cases hlo : ‖x‖ < innerRadius ψ r₀ h
  · exact Or.inl hlo
  · right
    by_contra hhi
    apply hxs
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using not_lt.mp hhi,
      by simpa only [Metric.mem_ball, dist_zero_right] using hlo⟩

end PfHk.AnnularSupportGeometry
