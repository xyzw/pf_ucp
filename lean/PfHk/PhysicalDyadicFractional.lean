import PfHk.PhysicalComparisonSpectral
import PfHk.DyadicFractional

/-! The fractional annular sum for the actual comparison operator.
The supplied endpoint sums concern its inclusion and graph image, and
the spectral interpolation acts on that same graph. -/

noncomputable section
namespace PfHk.PhysicalDyadicFractional

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalOperatorDomain PfHk.DyadicFractional

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFReference.ordinary
  PhysicalPFReference.radiation

variable {I : Type} [Fintype I] [DecidableEq I]

theorem comparison_fractional_sum {J : Type*}
    (spectral : ComparisonSpectralCalculus (I := I)) (S : Finset J)
    (u : J → Reference I (fun _ => 0)) (L : J → WaveSpace I)
    (hL : ∀ j, IsComparisonPair (fun _ => 0) (u j) (L j))
    (β R : J → ℝ) {τ s C₀ C₂ F : ℝ}
    (hτ : 0 < τ) (hs : 0 ≤ s) (hs2 : s ≤ 2)
    (hβ : ∀ j ∈ S, 0 < β j) (hR : ∀ j ∈ S, 0 < R j)
    (hzero : (∑ j ∈ S, coefficient τ (β j) (R j) 0 *
      ‖inclusion I (fun _ => 0) (u j)‖ ^ 2) ≤ C₀ * F)
    (hsecond : (∑ j ∈ S, coefficient τ (β j) (R j) 2 * ‖L j‖ ^ 2) ≤ C₂ * F) :
    (∑ j ∈ S, coefficient τ (β j) (R j) s *
      ‖spectral.fractional s (u j) ⟨L j, hL j⟩‖ ^ 2) ≤
        ((s / 2) * C₂ + (1 - s / 2) * C₀) * F := by
  exact fractional_sum S (fun j => inclusion I (fun _ => 0) (u j)) L
    (fun j => spectral.fractional s (u j) ⟨L j, hL j⟩) β R
    hτ hs hs2 hβ hR (fun j _ =>
      (spectral.interpolation s hs hs2 (u j) ⟨L j, hL j⟩ (L j) (hL j)).trans_eq
        (mul_comm _ _)) hzero hsecond

end PfHk.PhysicalDyadicFractional
