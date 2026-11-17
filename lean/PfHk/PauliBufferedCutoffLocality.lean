import PfHk.BufferedCutoffLocality

/-! Buffered cutoffs annihilate every mixed second derivative on waves
supported in the inner ball. The mixed statement is needed for the
off-diagonal terms in a Pauli contraction. -/

noncomputable section
namespace PfHk.PauliBufferedCutoffLocality

open MeasureTheory GptLean GptLean.PhysicalPFReference
  GptLean.ElectronicH1Space GptLean.ElectronicH1Multiplier
  PfHk.SmoothCutoffBounds PfHk.PhysicalCutoffCommutator
  PfHk.BufferedCutoffLocality

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 30000

variable {I H : Type} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cutoff_action_mixed {O : Position I} (family : BufferedFamily O)
    {r : ℝ} (hr : 0 < r) (u : L2 H I)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball O r → u x = 0) :
    (family.cutoff r).scalar.multiplier u = u ∧
      (∀ i, ((family.cutoff r).derivative i).multiplier u = 0) ∧
      ∀ i j, ((family.cutoff r).derivative i).derivativeMultiplier j u = 0 := by
  have h := cutoff_action family hr u hs
  refine ⟨h.1, h.2.1, ?_⟩
  intro i j
  apply (derivativeMultiplier_eq_of_supported ((family.cutoff r).derivative i) j u hs 0 ?_).trans
    (zero_smul _ _)
  intro x hx
  exact (buffered_derivatives_supported (family.cutoff r) hr (family.weight r hr) x
    (fun h => h.2 hx)).2 i j

end PfHk.PauliBufferedCutoffLocality
