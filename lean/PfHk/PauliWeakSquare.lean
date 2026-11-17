import PfHk.PauliClassicalCurlCross
import PfHk.PauliPhysicalCovariantCommutator
import PfHk.PauliSquareForm

/-! The physical weak Pauli square with a distributional classical curl.
The actual compactly supported spinors belong only to the reference and
external form domains. No comparison operator domain, classical magnetic
L2 source, smooth external potential, or assumed field commutator occurs
in the endpoint. -/

noncomputable section
namespace PfHk.PauliWeakSquare

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PhysicalLocalEnergy
  PfHk.PhysicalFieldRegularity PfHk.CenteredPhysicalReference
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
  PfHk.FriedrichsDivergenceBackground PfHk.PauliClassicalCurl
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion ordinary roughMultiply
  covariant externalCovariant PauliMagneticOperator.component

variable {N : ℕ}
  (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence)
  (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff) (e : ℝ)
  (hUV : CarlemanUV χ) (W : ConcreteWeylLaw photonMeasure)
  (G : StandardWeylGraphC1 W) (D : StandardWeylFormCoreDensity W G)
  (A B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
  (o : Fin N → GptLean.PhysicalSourceCoordinates.Position)
  (ρ : Fin N → ℝ) (hρ : ∀ n, 0 < ρ n) (p : ℝ) (hp : 2 < p)
  (hA : ∀ n k, MemLp (A n k) 6 (volume.restrict (Metric.ball (o n) (ρ n))))
  (hB : ∀ n k, MemLp (B n k) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball (o n) (ρ n))))

include S spectral joint A B o ρ hρ p hp hA hB in
/-- Every classical magnetic matrix entry is an actual integrable form
pairing at the local coefficient regularity of the manuscript. -/
theorem curl_pairings_integrable (z u : Ref N)
    (hus : ∀ n t, SupportedInCoordinate n (Metric.ball (o n) (ρ n / 2))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u t))) :
    ∀ n k s t, Integrable
      (PauliClassicalCurlForm.weightedInner (CoordinateSobolev.coordinateCoefficient n (B n k))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u t))) volume := by
  intro n k s t
  exact local_pairing_integrable S spectral joint n (o n) (hρ n) hp
    (k + 1) (k + 2) (A n) (B n k) (hA n) (hB n k) (u t) (z s) (hus n t)

include S spectral joint friedrichs W G D hρ p hp hA hB in
/-- The local weak Pauli-square identity for the actual physical kernels
and external form, with distributional curl and exact Zeeman coefficients. -/
theorem weak_square_on_balls
    (hcurl : ∀ n k, WeakCurlPairOn (Metric.ball (o n) (ρ n))
      (A n) (k + 1) (k + 2) (B n k))
    (positive negative : Configuration N → ℝ) (z u : Ref N)
    (hz : Domain (configurationVector A) positive negative z)
    (hu : Domain (configurationVector A) positive negative u)
    (hzc : ∀ s, CompactlySupportedIn Set.univ (z s))
    (huc : ∀ t, CompactlySupportedIn Set.univ (u t))
    (hzs : ∀ n s, SupportedInCoordinate n (Metric.ball (o n) (ρ n / 2))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)))
    (hus : ∀ n t, SupportedInCoordinate n (Metric.ball (o n) (ρ n / 2))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u t))) :
    rawForm C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
      (profile_bound F χ 0) e (configurationVector A) positive negative z u hz hu =
    PauliOrbitalForm.form C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
      (profile_bound F χ 0) e (configurationVector A) positive negative z u hz hu +
      PauliSquareForm.classicalForm B z u +
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (PauliMagneticOperator.quantum F χ hUV C e u s) := by
  apply PauliSquareForm.of_component_commutators C
    (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
    (profile_bound F χ 0) e F χ hUV (configurationVector A) positive negative B z u hz hu
  intro n k s t
  have hne : (k + 1 : Fin 3) ≠ k + 2 := by fin_cases k <;> decide
  have hc := local_cross_pair S spectral joint friedrichs C
    (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
    (profile_bound F χ 0) e n (o n) (hρ n) hp
    (k + 1) (k + 2) hne (A n) (B n k) (hA n) (hB n k) (hcurl n k)
    (u t) (z s) (fun a => (hu t).vector (n, a)) (fun a => (hz s).vector (n, a))
    (hus n t) (hzs n s)
  exact PauliPhysicalCovariantCommutator.cross_of_classical C F χ e hUV W G D
    (configurationVector A) positive negative n k (z s) (u t) (hz s) (hu t)
    (hzc s) (huc t) _ hc

end PfHk.PauliWeakSquare

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
