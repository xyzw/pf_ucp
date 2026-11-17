import PfHk.WeightedDyadicCutoffs
import PfHk.L2ScalarNorm

/-! Only finitely many actual weighted cutoff vectors survive for an
L2 field which vanishes on a neighborhood of the center. -/

noncomputable section
namespace PfHk.SmoothDyadicCutoffs

open MeasureTheory PfHk.SmoothCutoffBounds PfHk.PhysicalCutoffCommutator
  GptLean.ElectronicH1Space PfHk

set_option Elab.async false
set_option maxHeartbeats 30000

variable {I H : Type} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {O : EuclideanSpace ℝ I}

theorem weightedCutoff_multiplier_eventually_zero (family : BufferedFamily O)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (τ α : ℝ) (u : L2 H I)
    (hu : ∀ᵐ x ∂volume, dist x O < ρ → u x = 0) :
    ∃ J : ℕ, ∀ j, J ≤ j → (weightedCutoff family R hR τ α j).scalar.multiplier u = 0 := by
  obtain ⟨J, hJ⟩ := weightedCutoff_eventually_zero_outside family hR hρ τ α
  refine ⟨J, ?_⟩
  intro j hj
  apply Lp.ext
  filter_upwards [hu, scalar_multiplier_ae (weightedCutoff family R hR τ α j).scalar u,
    (Lp.coeFn_zero H 2 volume)] with x hux hx hz
  simp only [Pi.zero_apply] at hz
  rw [hx, hz]
  by_cases hi : dist x O < ρ
  · rw [hux hi, smul_zero]
  · rw [hJ j hj x (le_of_not_gt hi), zero_smul]

end PfHk.SmoothDyadicCutoffs
