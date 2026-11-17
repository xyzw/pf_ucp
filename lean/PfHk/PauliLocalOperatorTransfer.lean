import PfHk.PauliMagneticOperatorForm
import PfHk.PauliOrbitalCutoffLocality
import PfHk.PauliMagneticCutoffLocality
import PfHk.PauliWeakSquare

/-! Transfer of a local Pauli weak equation to a global operator with
independently truncated orbital and magnetic coefficients. The local
weak Pauli square is used on compact form vectors only. -/

noncomputable section
namespace PfHk.PauliLocalOperatorTransfer

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  GptLean.ElectronicH1Multiplier PfHk.PauliSpin PfHk.PauliGroundState
  PfHk.PhysicalLocalEnergy PfHk.PhysicalFieldRegularity PfHk.CenteredPhysicalReference
  PfHk.PhysicalCoefficientLocality PfHk.PhysicalCutoffCommutator
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
  PfHk.FriedrichsDivergenceBackground PfHk.PauliClassicalCurl
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion roughMultiply externalForm
  rawForm PauliOrbitalForm.form PauliSquareForm.classicalForm
  PauliMagneticOperator.quantum DifferentiableMultiplier.multiplier

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure)
  (F : Frame) (χ : ArticleCutoff) (e : ℝ)

/-- The Pauli form equation against form spinors supported in a region. -/
def IsLocalOperatorPair
    (A : (Fin N × Fin 3) → Configuration N → ℝ)
    (positive negative : Configuration N → ℝ) (Ω : Set (Configuration N))
    (u : Ref N) (hu : Domain A positive negative u)
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3)) : Prop :=
  ∀ z hz, (∀ s, ∀ᵐ X ∂volume, X ∉ Ω →
      inclusion (Fin N × Fin 3) (fun _ => 0) (z s) X = 0) →
    rawForm C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
      (profile_bound F χ 0) e A positive negative z u hz hu =
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) (f s)

variable (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence)
  (hUV : CarlemanUV χ) (W : ConcreteWeylLaw photonMeasure)
  (G : StandardWeylGraphC1 W) (D : StandardWeylFormCoreDensity W G)
  (A B B' : Fin N → Fin 3 → PhysicalSourceCoordinates.Position → ℝ)
  (o : Fin N → PhysicalSourceCoordinates.Position)
  (ρ : Fin N → ℝ) (hρ : ∀ n, 0 < ρ n) (p : ℝ) (hp : 2 < p)
  (hA : ∀ n k, MemLp (A n k) 6 (volume.restrict (Metric.ball (o n) (ρ n))))
  (hB : ∀ n k, MemLp (B n k) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball (o n) (ρ n))))
  (hcurl : ∀ n k, WeakCurlPairOn (Metric.ball (o n) (ρ n))
    (A n) (k + 1) (k + 2) (B n k))
  (positive negative : Configuration N → ℝ)
  (b : PhysicalExternalCoefficients.Data N)

include S spectral joint friedrichs W G D hρ p hp hA hB hcurl in
theorem operatorPair_of_local
    (a : TwiceDifferentiableMultiplier (Fin N × Fin 3)) {Ω : Set (Configuration N)}
    (hs : ∀ X, X ∉ Ω → a.scalar.weight X = 0)
    (hAv : ∀ i X, a.scalar.weight X ≠ 0 → configurationVector A i X = b.vector i X)
    (hpv : ∀ X, a.scalar.weight X ≠ 0 → positive X = b.positive X)
    (hnv : ∀ X, a.scalar.weight X ≠ 0 → negative X = b.negative X)
    (hBeq : ∀ n k x, x ∈ Metric.ball (o n) (ρ n / 2) → B n k x = B' n k x)
    (u : Ref N) (hu : Domain (configurationVector A) positive negative u)
    (hu' : Domain b.vector b.positive b.negative u)
    (hU : ∀ s, Agreement (configurationVector A) b.vector positive negative b.positive b.negative
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))
    (hfix : ∀ s, a.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    (hfirst : ∀ i s, (a.derivative i).multiplier
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0)
    (hsecond : ∀ i s, (a.derivative i).derivativeMultiplier i
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0)
    (huc : ∀ s, CompactlySupportedIn Set.univ (u s))
    (hus : ∀ n s, SupportedInCoordinate n (Metric.ball (o n) (ρ n / 2))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))
    (hzc : ∀ z : Ref N, ∀ s, CompactlySupportedIn Set.univ (PauliLocalEnergy.localize a.scalar z s))
    (hzs : ∀ z : Ref N, ∀ n s, SupportedInCoordinate n (Metric.ball (o n) (ρ n / 2))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (PauliLocalEnergy.localize a.scalar z s)))
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hf : IsLocalOperatorPair C F χ e (configurationVector A) positive negative Ω u hu f) :
    PauliMagneticOperatorRealization.IsOperatorPair b C
      (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
      e F χ hUV B' u hu' (fun s => a.scalar.multiplier (f s)) := by
  intro z hz
  let az := PauliLocalEnergy.localize a.scalar z
  have haz (s : SpinIndex N) := agreement_localize (fun _ => 0)
    (configurationVector A) b.vector positive negative b.positive b.negative a.scalar (z s)
    hAv hpv hnv
  have hzold : Domain (configurationVector A) positive negative az := fun s =>
    domain_congr (fun _ => 0) b.vector (configurationVector A) b.positive b.negative positive negative
      (az s) ((hz s).localize (fun _ => 0) a.scalar)
      (Agreement.symm _ _ _ _ _ _ (haz s))
  have heq := hf az hzold (fun s => localized_supported (fun _ => 0) a.scalar hs (z s))
  have hsq := PauliWeakSquare.weak_square_on_balls S spectral joint friedrichs C F χ e hUV W G D
    A B o ρ hρ p hp hA hB hcurl positive negative az u hzold hu (hzc z) huc (hzs z) hus
  have horb : PauliOrbitalForm.form C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (configurationVector A) positive negative
      az u hzold hu =
    PauliOrbitalForm.form C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e b.vector b.positive b.negative
      az u (PauliLocalEnergy.domain_localize hz a.scalar) hu' := by
    unfold PauliOrbitalForm.form
    exact Finset.sum_congr rfl fun s _ => PhysicalCoefficientLocality.form_congr (fun _ => 0)
      (configurationVector A) b.vector positive negative b.positive b.negative
      C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
      (az s) (u s) (hzold s) (hu s) ((hz s).localize (fun _ => 0) a.scalar) (hu' s) (haz s) (hU s)
  have hmag := PauliMagneticCutoffLocality.classical_coefficient_congr B B'
    (fun n => Metric.ball (o n) (ρ n / 2)) hBeq az u hus
  have hcutorb := PauliOrbitalCutoffLocality.form_localize_left C
    (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
    b.vector b.positive b.negative a z u hz hu' hfix hfirst hsecond
  have hcutmag := PauliMagneticCutoffLocality.classical_localize_left a.scalar B' z u hfix
  have hcutquantum := PauliMagneticCutoffLocality.quantum_localize_left F χ hUV C e a.scalar z u hfix
  have hform := congrArg₂ (fun x y : ℂ => x + y)
    (congrArg₂ (fun x y : ℂ => x + y) (horb.trans hcutorb) (hmag.trans hcutmag)) hcutquantum
  have hpair : (∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (az s)) (f s)) =
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) (a.scalar.multiplier (f s)) :=
    Finset.sum_congr rfl fun s _ =>
      (congrArg (fun w : WaveSpace (Fin N × Fin 3) => inner ℂ w (f s))
        (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) a.scalar (z s))).trans
          (a.scalar.multiplier_symmetric (H := PhotonFock) _ _).symm
  exact hform.symm.trans (hsq.symm.trans (heq.trans hpair))

end PfHk.PauliLocalOperatorTransfer

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
