import PfHk.PauliLocalDomainIdentification
import PfHk.PauliGroundState

/-! Local operator-domain identification for the manuscript's actual
admissible potentials. No external multiplier-domain premise remains. -/

noncomputable section
namespace PfHk.PauliLocalDomain

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  GptLean.PhysicalPairDuality PfHk.PhysicalCommonFormDomain
  PfHk.PauliGroundState PfHk.PauliSpin PfHk.PhysicalLocalEnergy
  PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain PfHk.CenteredPhysicalReference
  PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
  PfHk.FriedrichsDivergenceBackground PfHk.KatoRellichBackground
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion

variable {N : ℕ} (A : VectorPotential) (v : ScalarPotential) (c : ℝ)
  (O : Configuration N) (ρ : ℝ)

/-- Ordinary local coefficient regularity at the chosen configuration. -/
structure PhysicalRegularity where
  exponent : ℝ
  exponent_gt_two : 2 < exponent
  divergence : PhysicalSourceCoordinates.Position → ℝ
  magnetic : Fin 3 → PhysicalSourceCoordinates.Position → ℝ
  vector_memLp : ∀ n k, MemLp (vectorCoefficient A n k) 6
    (volume.restrict (Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ))
  divergence_memLp : ∀ n, MemLp divergence (ENNReal.ofReal exponent)
    (volume.restrict (Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ))
  scalar_memLp : ∀ n, MemLp (v.val : PhysicalSourceCoordinates.Position → ℝ)
    (ENNReal.ofReal exponent)
    (volume.restrict (Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ))
  coulomb_memLp : MemLp (fun X => c * PhysicalCoulombH1.potential N X) ∞
    (volume.restrict (Metric.ball O ρ))
  weakDivergence : ∀ n, WeakDivergenceOn (Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ)
    (vectorCoefficient A n) divergence
  magnetic_memLp : ∀ n k, MemLp (magnetic k) (ENNReal.ofReal exponent)
    (volume.restrict (Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ))
  weakCurl : ∀ n k, PauliClassicalCurl.WeakCurlPairOn
    (Metric.ball (PhysicalSourceCoordinates.split n O).1 ρ)
    (vectorCoefficient A n) (k + 1) (k + 2) (magnetic k)

def PhysicalRegularity.data (a : PhysicalRegularity A v c O ρ) : Data O ρ where
  orbital := {
    vectorCoefficient := vectorCoefficient A
    divergenceCoefficient := fun _ => a.divergence
    scalarCoefficient := fun _ => (v.val : PhysicalSourceCoordinates.Position → ℝ)
    boundedCoefficient := fun X => c * PhysicalCoulombH1.potential N X
    divergenceExponent := a.exponent
    scalarExponent := a.exponent
    divergenceExponent_gt_two := a.exponent_gt_two
    scalarExponent_gt_two := a.exponent_gt_two
    vector_memLp := a.vector_memLp
    divergence_memLp := a.divergence_memLp
    scalar_memLp := a.scalar_memLp
    bounded_memLp := a.coulomb_memLp
    weakDivergence := a.weakDivergence }
  magnetic := fun _ => a.magnetic
  exponent := a.exponent
  exponent_gt_two := a.exponent_gt_two
  magnetic_memLp := a.magnetic_memLp
  weakCurl := a.weakCurl

variable {A v c O ρ}

/-- For physical admissible potentials, local weak Pauli operator
membership is exactly comparison-domain membership on inner-supported
reference spinors. All form multiplication domains are supplied by the
proved common physical form-domain theorem. -/
theorem physical_comparison_domain_iff_local_operatorPair
    (a : PhysicalRegularity A v c O ρ) (hρ : 0 < ρ) (hc : 0 ≤ c)
    (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff) (e : ℝ)
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (friedrichs : StandardFriedrichsDivergence) (hUV : CarlemanUV χ)
    (W : ConcreteWeylLaw photonMeasure) (G : StandardWeylGraphC1 W)
    (D : StandardWeylFormCoreDensity W G) (KR : StandardKatoRellich)
    (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e)
    (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e)
    (hSA : SelfAdjointGraph (PhysicalExternalOperator.freeHilbertGraph (fun _ => 0) C
      (profile (N := N) F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e))
    (u : Ref N)
    (hs : ∀ s, ∀ᵐ X ∂volume, X ∉ Metric.ball O (ρ / 8) →
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X = 0) :
    (∀ s, ComparisonDomain (fun _ => 0) (u s)) ↔
      ∃ f : SpinIndex N → WaveSpace (Fin N × Fin 3),
        PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e (vector A)
          (positive v c) (negative v c) (Metric.ball O (ρ / 2))
          u (physicalDomain A v c hc u) f := by
  exact comparison_domain_iff_local_operatorPair (PhysicalRegularity.data A v c O ρ a) hρ C F χ e
    S spectral joint friedrichs hUV W G D KR hD hG hSA
    u (physicalDomain A v c hc u) hs

end PfHk.PauliLocalDomain

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
