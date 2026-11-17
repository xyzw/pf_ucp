import PfHk.PauliLocalCutoffEquation
import PfHk.PauliPhysicalOperatorDomain

/-! Compact localization of a physical Pauli weak eigenstate belongs
to the actual comparison operator domain. The exact L2 source is
constructed by the cutoff equation, rather than assumed. -/

noncomputable section
namespace PfHk.PauliLocalDomain

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  GptLean.PhysicalPairDuality PfHk.PhysicalCommonFormDomain
  PfHk.PauliGroundState PfHk.PauliSpin PfHk.PauliLocalEnergy PfHk.PhysicalLocalEnergy
  PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain PfHk.CenteredPhysicalReference
  PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference PfHk.SmoothCutoffBounds
  PfHk.FriedrichsDivergenceBackground PfHk.KatoRellichBackground

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion rawForm
  PhysicalPFScalarMultiplier.multiply PauliLocalEnergy.localize

variable {N : ℕ} {O : Configuration N} {ρ : ℝ}
  (a : Data O ρ) (hρ : 0 < ρ)
  (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff) (e : ℝ)
  (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence)
  (hUV : CarlemanUV χ) (W : ConcreteWeylLaw photonMeasure)
  (G : StandardWeylGraphC1 W) (D : StandardWeylFormCoreDensity W G)
  (KR : StandardKatoRellich)
  (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hSA : SelfAdjointGraph (PhysicalExternalOperator.freeHilbertGraph (fun _ => 0) C
    (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e))

include hρ S spectral joint friedrichs hUV W G D KR hD hG hSA in
theorem localized_eigenstate_comparison_domain (family : BufferedFamily O) {r : ℝ}
    (hr : 0 < r) (hrρ : r ≤ ρ / 32) (E : ℝ) (u : Ref N)
    (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
      a.orbital.negative E u hu) :
    ∀ s, ComparisonDomain (fun _ => 0) (localize (family.cutoff r).scalar u s) := by
  have hf := PauliLocalCutoffEquation.eigenstate_local_operatorPair a hρ C F χ e
    S spectral joint friedrichs hUV W G D family hr hrρ E u hu heigen
  have hs := PauliLocalCutoffRules.localized_supported_radius family hr
    (show 2 * r ≤ ρ / 8 by linarith only [hrρ, hρ]) u
  exact comparison_domain_of_local_operatorPair a hρ C F χ e S spectral joint friedrichs
    hUV W G D KR hD hG hSA (localize (family.cutoff r).scalar u)
    (domain_localize hu (family.cutoff r).scalar) hs
    (PauliLocalCutoffEquation.source a C F χ e (family.cutoff r) E u hu) hf

variable {A : VectorPotential} {v : ScalarPotential} {c : ℝ}

include hρ S spectral joint friedrichs hUV W G D in
theorem physical_localized_eigenstate_source
    (areg : PhysicalRegularity A v c O ρ) (hc : 0 ≤ c)
    (family : BufferedFamily O) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ / 32)
    (E : ℝ) (u : Ref N)
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u)) :
    PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e (vector A) (positive v c)
      (negative v c) (Metric.ball O (ρ / 2)) (localize (family.cutoff r).scalar u)
      (physicalDomain A v c hc (localize (family.cutoff r).scalar u))
      (PauliLocalCutoffEquation.source (PhysicalRegularity.data A v c O ρ areg)
        C F χ e (family.cutoff r) E u (physicalDomain A v c hc u)) := by
  exact PauliLocalCutoffEquation.eigenstate_local_operatorPair
    (PhysicalRegularity.data A v c O ρ areg) hρ C F χ e S spectral joint friedrichs hUV W G D
    family hr hrρ E u (physicalDomain A v c hc u) heigen

include hρ S spectral joint friedrichs hUV W G D KR hD hG hSA in
/-- The manuscript's actual global coefficient classes provide every
multiplier-domain witness for the localized eigenstate conclusion. -/
theorem physical_localized_eigenstate_comparison_domain
    (areg : PhysicalRegularity A v c O ρ) (hc : 0 ≤ c)
    (family : BufferedFamily O) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ / 32)
    (E : ℝ) (u : Ref N)
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u)) :
    ∀ s, ComparisonDomain (fun _ => 0) (localize (family.cutoff r).scalar u s) := by
  exact localized_eigenstate_comparison_domain (PhysicalRegularity.data A v c O ρ areg)
    hρ C F χ e S spectral joint friedrichs hUV W G D KR hD hG hSA
    family hr hrρ E u (physicalDomain A v c hc u) heigen

end PfHk.PauliLocalDomain
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
