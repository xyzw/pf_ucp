import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Universal positive spectral calculus for a specified graph and form. -/

noncomputable section
namespace PfHk.ComparisonSpectralAlgebra

open scoped InnerProductSpace

variable {I Q W : Type*} [Fintype I]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

structure Data (J : Q →L[ℂ] W) (D : I → Q →L[ℂ] W)
    (R : Q →L[ℂ] W) (P : Q → W → Prop) where
  root : Q →L[ℂ] W
  root_form : ∀ u : Q, ‖root u‖ ^ 2 =
    (∑ i, ‖D i u‖ ^ 2) + ‖R u‖ ^ 2 + ‖J u‖ ^ 2
  root_graph : ∀ (u : Q) (L : W), P u L → ∀ v : Q, ⟪root v, root u⟫_ℂ = ⟪J v, L⟫_ℂ
  fractional : ℝ → (u : Q) → (∃ L, P u L) → W
  fractional_zero : ∀ u hu, fractional 0 u hu = J u
  fractional_one : ∀ u hu, fractional 1 u hu = root u
  fractional_two : ∀ u hu L, P u L → fractional 2 u hu = L
  interpolation : ∀ s, 0 ≤ s → s ≤ 2 → ∀ u hu L, P u L →
    ‖fractional s u hu‖ ^ 2 ≤ (‖J u‖ ^ 2) ^ (1 - s / 2) * (‖L‖ ^ 2) ^ (s / 2)

theorem form_le_graph {J : Q →L[ℂ] W} {D : I → Q →L[ℂ] W}
    {R : Q →L[ℂ] W} {P : Q → W → Prop} (S : Data J D R P)
    {u : Q} {L : W} (hL : P u L) :
    (∑ i, ‖D i u‖ ^ 2) + ‖R u‖ ^ 2 + ‖J u‖ ^ 2 ≤ ‖J u‖ * ‖L‖ := by
  have hroot : ‖S.root u‖ ^ 2 = (⟪J u, L⟫_ℂ).re :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (S.root u)).trans
      (congrArg Complex.re (S.root_graph u L hL u))
  exact ((S.root_form u).symm.trans hroot).le.trans (re_inner_le_norm (𝕜 := ℂ) _ _)

end PfHk.ComparisonSpectralAlgebra
