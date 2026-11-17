import GptLean.PhysicalSourcePair
import GptLean.PhysicalEnsembleH1

/-! Actual marginal density-current pairs for finite-kinetic-energy ensembles. -/

noncomputable section

namespace GptLean.PhysicalSourcePair

open MeasureTheory GptLean.ElectronicH1Space GptLean.PhysicalPairSpace
open GptLean.PhysicalEnsembleSource GptLean.PhysicalEnsembleH1
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

instance countFiber_separable : TopologicalSpace.SeparableSpace (Fiber H) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

/-- A finite-kinetic-energy ensemble gives an actual marginal pair without
a separate ensemble H1 or marginal L6 hypothesis. -/
def ofEnsemble (i : Fin N) (v : ℕ → H1 H (Fin N × Fin 3))
    (hv : Summable (fun n => ‖value (v n)‖ ^ 2))
    (hd : ∀ b, Summable (fun n => ‖derivative b (v n)‖ ^ 2))
    (d : Fin 3 → ℕ → L2 H (Fin N × Fin 3))
    (hcov : ∀ a, Summable (fun n => ‖d a n‖ ^ 2)) : Pair :=
  ofWaveFunction i (ensembleH1 v hv hd) (fun a => ensemble (d a) (hcov a))

theorem integral_density_ofEnsemble (i : Fin N) (v : ℕ → H1 H (Fin N × Fin 3))
    (hv : Summable (fun n => ‖value (v n)‖ ^ 2))
    (hd : ∀ b, Summable (fun n => ‖derivative b (v n)‖ ^ 2))
    (d : Fin 3 → ℕ → L2 H (Fin N × Fin 3))
    (hcov : ∀ a, Summable (fun n => ‖d a n‖ ^ 2)) :
    (∫ x, densityL1 (ofEnsemble i v hv hd d hcov) x) =
      (N : ℝ) * ∑' n, ‖value (v n)‖ ^ 2 := by
  exact (integral_density_ofWaveFunction i (ensembleH1 v hv hd)
    (fun a => ensemble (d a) (hcov a))).trans
      (congrArg (fun t : ℝ => (N : ℝ) * t) (norm_value_ensembleH1_sq v hv hd))

end GptLean.PhysicalSourcePair
