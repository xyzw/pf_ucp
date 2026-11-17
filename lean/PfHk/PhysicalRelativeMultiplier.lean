import PfHk.SpectralInterpolationSmallness
import PfHk.InfinitesimalBound

/-! Every derived fractional multiplier endpoint of order below two is
infinitesimally bounded relative to the actual comparison graph. -/

noncomputable section
namespace PfHk.PhysicalRelativeMultiplier

open GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalOperatorDomain PfHk.PhysicalDyadicIntegralFractional

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

attribute [local irreducible] PhysicalPFReference.inclusion
  PhysicalPFReference.ordinary PhysicalPFReference.radiation

variable {I : Type} [Fintype I] [DecidableEq I] {X : Type*}

theorem of_fractional_norm_sq (spectral : ComparisonSpectralCalculus (I := I))
    (u : X → Reference I (fun _ => 0)) (L T : X → WaveSpace I)
    (hL : ∀ x, IsComparisonPair (fun _ => 0) (u x) (L x))
    {s B : ℝ} (hs : 0 ≤ s) (hs2 : s < 2) (hB : 0 ≤ B)
    (hb : ∀ x, ‖T x‖ ^ 2 ≤ B * fractionalNormSq spectral s (u x) ⟨L x, hL x⟩) :
    InfinitesimalBound.Bound (fun x => ‖L x‖)
      (fun x => ‖inclusion I (fun _ => 0) (u x)‖) (fun x => ‖T x‖) := by
  apply InfinitesimalBound.of_squared (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _)
  apply InfinitesimalBound.squared_scale hB hb
  intro δ hδ
  have hex := SpectralInterpolationSmallness.fractional_norm_sq spectral hs hs2 hδ
  let K := Classical.choose hex
  have hk := Classical.choose_spec hex
  exact ⟨K, hk.1, fun x => hk.2 (u x) (L x) (hL x)⟩

end PfHk.PhysicalRelativeMultiplier
