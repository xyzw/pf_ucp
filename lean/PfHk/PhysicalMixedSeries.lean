import PfHk.PhysicalFractionalCarleman
import PfHk.PhysicalEnlargedFractionalCarleman

/-! The actual mixed series with both endpoint constants explicit. This
allows the proved free estimates to pass through source absorption. -/

noncomputable section
namespace PfHk.PhysicalMixedSeries

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift
open PfHk.PhysicalOperatorDomain PfHk.PhysicalDyadicIntegralFractional
  PfHk.SmoothDyadicCutoffs PfHk.SmoothCutoffBounds PfHk.DyadicFractional
  PfHk.PhysicalDyadicEnergy

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [local irreducible] inclusion FreeGraph

variable {N : ℕ}

def Bound (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (u : ℕ → Reference (Fin N × Fin 3) (fun _ => 0))
    (β R : ℕ → ℝ) (τ C₀ C₂ source : ℝ) : Prop :=
  ∃ v : ℕ → WaveSpace (Fin N × Fin 3),
    ∃ hv : ∀ j, IsComparisonPair (fun _ => 0) (u j) (v j),
    ∀ s : ℝ, 0 ≤ s → s ≤ 2 →
      Summable (fun j => coefficient τ (β j) (R j) s *
        fractionalNormSq spectral s (u j) ⟨v j, hv j⟩) ∧
      (∑' j, coefficient τ (β j) (R j) s *
        fractionalNormSq spectral s (u j) ⟨v j, hv j⟩) ≤
        ((s / 2) * C₂ + (1 - s / 2) * C₀) * source

theorem Bound.transfer_source
    {spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3)}
    {u : ℕ → Reference (Fin N × Fin 3) (fun _ => 0)}
    {β R : ℕ → ℝ} {τ C₀ C₂ F G k : ℝ}
    (h : Bound spectral u β R τ C₀ C₂ F)
    (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂) (hsource : F ≤ k * G) :
    Bound spectral u β R τ (k * C₀) (k * C₂) G := by
  obtain ⟨v, hv, hseries⟩ := h
  refine ⟨v, hv, ?_⟩
  intro s hs hs2
  obtain ⟨hsummable, hbound⟩ := hseries s hs hs2
  refine ⟨hsummable, hbound.trans ?_⟩
  have hweight : 0 ≤ (s / 2) * C₂ + (1 - s / 2) * C₀ :=
    add_nonneg (mul_nonneg (by linarith) hC₂) (mul_nonneg (by linarith) hC₀)
  exact (mul_le_mul_of_nonneg_left hsource hweight).trans_eq (by ring)

theorem of_standard
    {spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3)}
    {O : Configuration N} {family : BufferedFamily O}
    {R τ α C₂ : ℝ} {hR : 0 < R}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {f : WaveSpace (Fin N × Fin 3)}
    (h : PhysicalFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂) :
    Bound spectral (PhysicalFractionalCarleman.localized family R hR τ α u)
      (dyadicBeta α R) (radius R) τ 6144 C₂ (∫ X, sourceEnergy O τ α f X) := h

theorem of_enlarged
    {spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3)}
    {O : Configuration N} {family : BufferedFamily O}
    {R τ α C₂ : ℝ} {hR : 0 < R}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {f : WaveSpace (Fin N × Fin 3)}
    (h : PhysicalEnlargedFractionalCarleman.MixedEstimate spectral family R hR τ α u f C₂) :
    Bound spectral (PhysicalEnlargedFractionalCarleman.localized family R hR τ α u)
      (dyadicBeta α R) (radius R) τ 40960 C₂ (∫ X, sourceEnergy O τ α f X) := h

end PfHk.PhysicalMixedSeries
