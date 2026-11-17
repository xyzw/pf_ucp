import PfHk.UniqueContinuationTransfer

/-! A single infinite-order zero starts the continuation argument.
The value of a chosen L2 representative at the center is immaterial. -/

noncomputable section
namespace PfHk.UniqueContinuation

open MeasureTheory Set
open PfHk.UniqueContinuationDensity

set_option maxHeartbeats 20000
set_option Elab.async false

variable {X H : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [NormedAddCommGroup H] {μ : Measure X}

theorem ae_zero_of_uniform_flat_seed {ψ : X → H} {U : Set X} {α : ℝ}
    (P : X → ℝ → ℝ → ℝ → Prop) (hα : 0 < α)
    (hU : IsPreconnected U) (hfull : ∀ᵐ x ∂μ, x ∈ U)
    (huniform : ∀ x₀ ∈ U, ∃ R₀ τ₀ K : ℝ,
      0 < R₀ ∧ R₀ ≤ Real.exp (-2) ∧ 1 ≤ τ₀ ∧ 0 ≤ K ∧
      Metric.ball x₀ (4 * R₀) ⊆ U ∧
      ∀ y ∈ Metric.ball x₀ R₀, ∀ R : ℝ, 0 < R → R ≤ R₀ → P y R τ₀ K)
    (hvanish : ∀ x₀ R τ₀ K, P x₀ R τ₀ K → 0 < R → R ≤ Real.exp (-2) → 0 ≤ K →
      (∀ s, 0 < s → s ≤ R / 4 →
        1 ≤ CarlemanWeights.beta α (-Real.log s) * s ^ (-2 : ℝ)) →
      InfiniteOrder.FlatAtZero (localMass (μ := μ) ψ x₀) →
        ∀ᵐ x ∂μ.restrict (Metric.ball x₀ (R / 4)), ψ x = 0)
    (hflat : ∃ x₀ ∈ U, InfiniteOrder.FlatAtZero (localMass (μ := μ) ψ x₀)) :
    ∀ᵐ x ∂μ, ψ x = 0 := by
  obtain ⟨Rcoef, hRcoef, _hcoefsmall, hcoef⟩ := exists_radius_mass_coefficient α hα
  have hlocal : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ∀ y, dist x y < r / 2 →
      InfiniteOrder.FlatAtZero (localMass (μ := μ) ψ y) →
      ∀ᵐ z ∂μ.restrict (Metric.ball y r), ψ z = 0 := by
    intro x hx
    obtain ⟨R₀, τ₀, K, hR₀, hR₀small, _hτ₀, hK, _hball, hP⟩ := huniform x hx
    let R := min R₀ Rcoef
    have hR : 0 < R := lt_min hR₀ hRcoef
    have hRR₀ : R ≤ R₀ := min_le_left _ _
    have hRRcoef : R ≤ Rcoef := min_le_right _ _
    refine ⟨R / 4, by positivity, ?_⟩
    intro y hxy hyflat
    have hy : y ∈ Metric.ball x R₀ := by
      rw [Metric.mem_ball, dist_comm]
      linarith
    exact hvanish y R τ₀ K (hP y hy R hR hRR₀) hR (hRR₀.trans hR₀small) hK
      (fun s hs hsR => hcoef s hs (by linarith)) hyflat
  obtain ⟨x₀, hxU, hxflat⟩ := hflat
  obtain ⟨r₀, hr₀, hz₀⟩ := hlocal x₀ hxU
  have hstart : (U ∩ zeroNeighborhoods μ ψ).Nonempty :=
    ⟨x₀, hxU, r₀, hr₀, hz₀ x₀ (by simp only [dist_self]; positivity) hxflat⟩
  apply ae_zero_of_local_propagation hU hfull hstart
  intro x hx
  obtain ⟨r, hr, hz⟩ := hlocal x hx
  exact ⟨r, hr, fun y hy hxy => hz y hxy (flat_of_zeroNeighborhood hy)⟩

end PfHk.UniqueContinuation
