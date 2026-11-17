import GptLean.ElectronicH1Complex
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith

/-! Universal ordinary weak-Laplacian and graph-norm interfaces, with
abstract Hilbert fibres so physical specialization does not unfold Fock
scalar instances during elaboration. -/

noncomputable section
namespace PfHk.ComparisonGraphAlgebra

open MeasureTheory GptLean
open scoped InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 40000

variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def WeakLaplacian (g : I → ElectronicH1Space.L2 H I) (l : ElectronicH1Space.L2 H I) : Prop :=
  ∀ v : ElectronicH1Complex.ComplexH1 H I,
    (∑ i, ⟪ElectronicH1Complex.derivative i v, g i⟫_ℂ) = ⟪ElectronicH1Complex.value v, l⟫_ℂ

theorem WeakLaplacian.congr {g g' : I → ElectronicH1Space.L2 H I}
    {l : ElectronicH1Space.L2 H I} (h : WeakLaplacian g l) (hg : ∀ i, g' i = g i) :
    WeakLaplacian g' l := by
  intro v
  exact (Finset.sum_congr rfl fun i _ =>
    congrArg (fun z : ElectronicH1Space.L2 H I => ⟪ElectronicH1Complex.derivative i v, z⟫_ℂ)
      (hg i)).trans (h v)

/-- Standard equivalence of two graph norms over a fixed inclusion. -/
structure GraphNormComparison {Q W : Type*} [NormedAddCommGroup W]
    (J : Q → W) (G P : Q → W → Prop) where
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  comparison_le : ∀ (u : Q) (f L : W), G u f → P u L → ‖L‖ ≤ bound * (‖f‖ + ‖J u‖)
  operator_le : ∀ (u : Q) (f L : W), G u f → P u L → ‖f‖ + ‖J u‖ ≤ bound * ‖L‖

private theorem square_graph_bound (a b c D : ℝ) (ha : 0 ≤ a)
    (h : a ≤ D * (b + c)) : a ^ 2 ≤ 2 * D ^ 2 * (b ^ 2 + c ^ 2) := by
  have hp := pow_le_pow_left₀ ha h 2
  have hn := mul_nonneg (sq_nonneg D) (sq_nonneg (b - c))
  nlinarith

theorem comparison_graph_bound {Q W : Type*} [NormedAddCommGroup W]
    {J : Q → W} {G P : Q → W → Prop} (hG : GraphNormComparison J G P)
    {u : Q} {f : W} (hf : G u f) (hD : ∃ L, P u L) :
    ∃ L, P u L ∧ ‖L‖ ^ 2 ≤ (2 * hG.bound ^ 2) * (‖f‖ ^ 2 + ‖J u‖ ^ 2) := by
  obtain ⟨L, hL⟩ := hD
  exact ⟨L, hL, square_graph_bound _ _ _ _ (norm_nonneg L) (hG.comparison_le u f L hf hL)⟩

end PfHk.ComparisonGraphAlgebra
