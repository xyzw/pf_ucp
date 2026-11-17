import PfHk.CoordinateSobolev
import PfHk.PhysicalDyadicSpectral

/-!
The ordinary joint spectral domination for coordinate Bessel potentials and
the comparison graph `-Δ + Hrad + 1`. Every bound uses the same fractional
image as the physical Carleman theorem. The background is independent of the
quantized field profile, charge, external coefficients and Carleman weight.

The fields below express the standard scalar inequalities for the commuting
electronic coordinate Laplacians and the radiation operator. They contain no
coefficient multiplier or covariant derivative estimate.
-/

noncomputable section
namespace PfHk.CoordinateComparisonSpectral

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalOperatorDomain PfHk.PhysicalDyadicIntegralFractional
open PfHk.CoordinateSobolev

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option maxHeartbeats 30000

attribute [local irreducible] PhysicalPFReference.inclusion
  PhysicalPFReference.ordinary PhysicalPFReference.radiation

variable {N : ℕ}

/-- Joint spectral calculus for the actual coordinate Fourier multipliers and
the already specified positive comparison operator. -/
structure Data (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3)) : Prop where
  form_value : ∀ (n : Fin N) (s : ℝ), 0 ≤ s → s ≤ 1 →
    ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0)),
      ∃ v : WaveSpace (Fin N × Fin 3),
        BesselPair (H := PhotonFock) n s (inclusion (Fin N × Fin 3) (fun _ => 0) u) v ∧
        ‖v‖ ≤ ‖spectral.root u‖
  value : ∀ (n : Fin N) (s t : ℝ), 0 ≤ s → s ≤ t → t ≤ 2 →
    ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0))
      (hu : ∃ v, IsComparisonPair (fun _ => 0) u v),
      ∃ v : WaveSpace (Fin N × Fin 3),
        BesselPair (H := PhotonFock) n s (inclusion (Fin N × Fin 3) (fun _ => 0) u) v ∧
        ‖v‖ ≤ ‖fractionalVector spectral t u hu‖
  ordinary : ∀ (n : Fin N) (i : Fin N × Fin 3)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ∃ v, IsComparisonPair (fun _ => 0) u v),
    ∃ v : WaveSpace (Fin N × Fin 3),
      BesselPair (H := PhotonFock) n (1 / 2)
        (PhysicalPFReference.ordinary (Fin N × Fin 3) (fun _ => 0) i u) v ∧
      ‖v‖ ≤ ‖fractionalVector spectral (3 / 2) u hu‖
  radiation : ∀ (n : Fin N)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ∃ v, IsComparisonPair (fun _ => 0) u v),
    ∃ v : WaveSpace (Fin N × Fin 3),
      BesselPair (H := PhotonFock) n (1 / 2)
        (PhysicalPFReference.radiation (Fin N × Fin 3) (fun _ => 0) u) v ∧
      ‖v‖ ≤ ‖fractionalVector spectral (3 / 2) u hu‖

end PfHk.CoordinateComparisonSpectral
