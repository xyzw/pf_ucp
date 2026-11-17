import PfHk.PhysicalOperatorCore

/-! Ordinary continuous compact source representatives for the supported
operator core. Their equations are supplied separately by the actual
form-realized graph. -/

noncomputable section
namespace PfHk.PhysicalOperatorDomain

open MeasureTheory GptLean.PhysicalFock GptLean.PhysicalPFReference

variable {I : Type} [Fintype I] [DecidableEq I]

structure CompactSource (s : Set (Position I)) (f : WaveSpace I) where
  representative : Position I → PhotonFock
  continuous : Continuous representative
  compact : HasCompactSupport representative
  support : tsupport representative ⊆ s
  agrees : f =ᵐ[volume] representative

end PfHk.PhysicalOperatorDomain
