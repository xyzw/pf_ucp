import PfHk.PhysicalDyadicFractional

/-! Typed spectral values and scalar squared norms for the concrete
comparison operator. These are definitions of its actual spectral image. -/

noncomputable section
namespace PfHk.PhysicalDyadicIntegralFractional

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalOperatorDomain PfHk.DyadicFractional

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.inclusion
  PhysicalPFReference.ordinary PhysicalPFReference.radiation

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The actual spectral image with its wave-space output type explicit. -/
def fractionalVector (spectral : ComparisonSpectralCalculus (I := I)) (s : ℝ)
    (u : Reference I (fun _ => 0))
    (hu : ∃ v : WaveSpace I, IsComparisonPair (fun _ => 0) u v) : WaveSpace I :=
  spectral.fractional s u hu

theorem comparisonPair_unique (spectral : ComparisonSpectralCalculus (I := I))
    {u : Reference I (fun _ => 0)} {v w : WaveSpace I}
    (hv : IsComparisonPair (fun _ => 0) u v)
    (hw : IsComparisonPair (fun _ => 0) u w) : v = w :=
  (spectral.fractional_two u ⟨v, hv⟩ v hv).symm.trans
    (spectral.fractional_two u ⟨v, hv⟩ w hw)

def fractionalNormSq (spectral : ComparisonSpectralCalculus (I := I)) (s : ℝ)
    (u : Reference I (fun _ => 0))
    (hu : ∃ v : WaveSpace I, IsComparisonPair (fun _ => 0) u v) : ℝ :=
  ‖fractionalVector spectral s u hu‖ ^ 2

theorem fractionalNormSq_nonneg (spectral : ComparisonSpectralCalculus (I := I)) (s : ℝ)
    (u : Reference I (fun _ => 0))
    (hu : ∃ v : WaveSpace I, IsComparisonPair (fun _ => 0) u v) :
    0 ≤ fractionalNormSq spectral s u hu := sq_nonneg _

theorem comparison_fractional_sum_normSq {J : Type*}
    (spectral : ComparisonSpectralCalculus (I := I)) (S : Finset J)
    (u : J → Reference I (fun _ => 0)) (v : J → WaveSpace I)
    (hv : ∀ j, IsComparisonPair (fun _ => 0) (u j) (v j))
    (β R : J → ℝ) {τ s C₀ C₂ F : ℝ}
    (hτ : 0 < τ) (hs : 0 ≤ s) (hs2 : s ≤ 2)
    (hβ : ∀ j ∈ S, 0 < β j) (hR : ∀ j ∈ S, 0 < R j)
    (hzero : (∑ j ∈ S, coefficient τ (β j) (R j) 0 * ‖inclusion I (fun _ => 0) (u j)‖ ^ 2) ≤ C₀ * F)
    (hsecond : (∑ j ∈ S, coefficient τ (β j) (R j) 2 * ‖v j‖ ^ 2) ≤ C₂ * F) :
    (∑ j ∈ S, coefficient τ (β j) (R j) s * fractionalNormSq spectral s (u j) ⟨v j, hv j⟩) ≤
      ((s / 2) * C₂ + (1 - s / 2) * C₀) * F := by
  simpa only [fractionalNormSq, fractionalVector] using
    PhysicalDyadicFractional.comparison_fractional_sum spectral S u v hv β R
      hτ hs hs2 hβ hR hzero hsecond

end PfHk.PhysicalDyadicIntegralFractional
