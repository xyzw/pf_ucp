import PfHk.PauliWeakSquare
import PfHk.PauliGroundState

/-! Specialization of the local weak Pauli square to the admissible
physical potentials and the Pauli form used for ground states. All
external multiplier-domain conditions are supplied by the proved common
form-domain theorem. -/

noncomputable section
namespace PfHk.PauliWeakSquare

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.PhysicalPairDuality GptLean.SymmetricLift
  GptLean.Representability
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PhysicalLocalEnergy
  PfHk.PhysicalFieldRegularity PfHk.CenteredPhysicalReference
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
  PfHk.FriedrichsDivergenceBackground PfHk.PauliClassicalCurl
  PfHk.PhysicalCommonFormDomain
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion ordinary roughMultiply
  covariant externalCovariant PauliMagneticOperator.component

variable {N : ℕ}

/-- The existing physical Pauli form is the orbital form plus the
classical and quantum Zeeman terms, on locally supported reference spinors. -/
theorem physical_weak_square_on_balls
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (friedrichs : StandardFriedrichsDivergence)
    (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff) (e : ℝ)
    (hUV : CarlemanUV χ) (W : ConcreteWeylLaw photonMeasure)
    (G : StandardWeylGraphC1 W) (D : StandardWeylFormCoreDensity W G)
    (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (o : Fin N → GptLean.PhysicalSourceCoordinates.Position)
    (ρ : Fin N → ℝ) (hρ : ∀ n, 0 < ρ n) (p : ℝ) (hp : 2 < p)
    (hA : ∀ n k, MemLp (vectorCoefficient A n k) 6
      (volume.restrict (Metric.ball (o n) (ρ n))))
    (hB : ∀ n k, MemLp (B n k) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball (o n) (ρ n))))
    (hcurl : ∀ n k, WeakCurlPairOn (Metric.ball (o n) (ρ n))
      (vectorCoefficient A n) (k + 1) (k + 2) (B n k))
    (z u : Ref N)
    (hzc : ∀ s, CompactlySupportedIn Set.univ (z s))
    (huc : ∀ t, CompactlySupportedIn Set.univ (u t))
    (hzs : ∀ n s, SupportedInCoordinate n (Metric.ball (o n) (ρ n / 2))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)))
    (hus : ∀ n t, SupportedInCoordinate n (Metric.ball (o n) (ρ n / 2))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u t))) :
    PauliGroundState.form C e F χ A v c hc z u =
      PauliOrbitalForm.form C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
        z u (physicalDomain A v c hc z) (physicalDomain A v c hc u) +
      PauliSquareForm.classicalForm B z u +
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (PauliMagneticOperator.quantum F χ hUV C e u s) := by
  exact weak_square_on_balls S spectral joint friedrichs C F χ e hUV W G D
    (vectorCoefficient A) B o ρ hρ p hp hA hB hcurl (positive v c) (negative v c)
    z u (physicalDomain A v c hc z) (physicalDomain A v c hc u) hzc huc hzs hus

end PfHk.PauliWeakSquare

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
