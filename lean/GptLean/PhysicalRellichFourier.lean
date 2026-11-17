import GptLean.PhotonLocalizationRellich
import Mathlib.Analysis.Fourier.LpSpace

/-!
The permitted universal supported H½ Rellich theorem is stated using
Mathlib's actual L2 Fourier transform. Its specialization fixes the same
Fourier map used by the physical finite-sector coordinate construction.
-/

noncomputable section

namespace GptLean.PhysicalRellichFourier

open MeasureTheory PhotonLocalization
open scoped ENNReal

/-- Universal supported fractional Rellich compactness, independent of physical data. -/
structure StandardSupportedHalfRellich where
  compact_half_ball : ∀ (I E : Type) [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] (s : Set (EuclideanSpace ℝ I)), Bornology.IsBounded s →
    IsCompact {u : Lp E 2 (volume : Measure (EuclideanSpace ℝ I)) |
      (∀ᵐ x ∂volume, x ∉ s → u x = 0) ∧
        (∫⁻ ξ, ENNReal.ofReal (Real.sqrt (1 + ‖ξ‖ ^ 2)) *
          ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ I) E u ξ‖ₑ ^ 2) ≤ 1}

variable (B : StandardSupportedHalfRellich) (N : ℕ) (E : ℕ → Type)
  [∀ m, NormedAddCommGroup (E m)] [∀ m, InnerProductSpace ℂ (E m)]
  [∀ m, CompleteSpace (E m)] [∀ m, FiniteDimensional ℂ (E m)]

/-- The actual sector Fourier map, with only the universal Rellich theorem as background. -/
def sectorBackground : SectorRellichBackground N E where
  fourier m := Lp.fourierTransformₗᵢ (PhotonSectorPosition N m) (E m)
  compact_half_ball m s hs := B.compact_half_ball (Fin (N + m) × Fin 3) (E m) s hs

@[simp] theorem sectorBackground_fourier (m : ℕ) :
    (sectorBackground B N E).fourier m =
      Lp.fourierTransformₗᵢ (PhotonSectorPosition N m) (E m) := rfl

end GptLean.PhysicalRellichFourier
