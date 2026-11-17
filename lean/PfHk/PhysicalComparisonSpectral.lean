import PfHk.PhysicalComparisonDomain
import PfHk.ComparisonSpectralAlgebra

/-! The standard positive spectral calculus for the concrete comparison
graph `-Δ + Hrad + 1`. The square-root form and fractional interpolation
refer to that same graph and its actual derivative coordinates. -/

noncomputable section
namespace PfHk.PhysicalOperatorDomain

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

local instance spectralPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFReference.ordinary
  PhysicalPFReference.radiation PhysicalPFReference.potential PhysicalPFReference.referenceSubspace
  ElectronicH1Complex.complexWeakGraph ElectronicH1Complex.derivative ElectronicH1Complex.value
  IsComparisonPair IsLaplacianPair IsRadiationPair

variable {I : Type} [Fintype I] [DecidableEq I]

local instance spectralWaveDirectInner : InnerProductSpace ℂ (WaveSpace I) :=
  { (inferInstance : InnerProductSpace ℂ (WaveSpace I)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (WaveSpace I)) }

/-- The positive spectral theorem, specialized to the already specified
comparison graph. All exponents use the convention `fractional s = L^(s/2)`. -/
abbrev ComparisonSpectralCalculus :=
  ComparisonSpectralAlgebra.Data (I := I) (Q := Reference I (fun _ => 0)) (W := WaveSpace I)
    (inclusion I (fun _ => 0))
    (fun i => ordinary I (fun _ => 0) i) (radiation I (fun _ => 0)) (IsComparisonPair (fun _ => 0))

/-- The first-order comparison form follows from the same positive
operator graph, by the ordinary Hilbert-space Cauchy inequality. -/
theorem comparison_form_le_graph (S : ComparisonSpectralCalculus (I := I))
    {u : Reference I (fun _ => 0)} {L : WaveSpace I}
    (hL : IsComparisonPair (fun _ => 0) u L) :
    (∑ i, ‖ordinary I (fun _ => 0) i u‖ ^ 2) +
      ‖radiation I (fun _ => 0) u‖ ^ 2 + ‖inclusion I (fun _ => 0) u‖ ^ 2 ≤
      ‖inclusion I (fun _ => 0) u‖ * ‖L‖ :=
  ComparisonSpectralAlgebra.form_le_graph S hL

end PfHk.PhysicalOperatorDomain
