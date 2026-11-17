import PfHk.PauliLocalOperatorDomain

/-! Both directions of the local domain identification. A reference
spinor supported in the inner ball has an L2 local Pauli source exactly
when each spin component belongs to the comparison operator domain. -/

noncomputable section
namespace PfHk.PauliLocalDomain

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.PauliGroundState PfHk.PauliSpin PfHk.PhysicalLocalEnergy
  PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain PfHk.CenteredPhysicalReference
  PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
  PfHk.FriedrichsDivergenceBackground PfHk.PhysicalCoefficientLocality
  PfHk.KatoRellichBackground PfHk.PhysicalExternalOperator
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion
  rawForm PauliOrbitalForm.form PauliSquareForm.classicalForm
  PauliMagneticOperator.quantum

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
  (hSA : SelfAdjointGraph (freeHilbertGraph (fun _ => 0) C
    (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e))

include hρ hUV S spectral joint friedrichs W G D KR hD hG hSA in
theorem exists_local_operatorPair_of_comparison_domain
    (u : Ref N) (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
    (hs : ∀ s, ∀ᵐ X ∂volume, X ∉ Metric.ball O (ρ / 8) →
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X = 0)
    (hc : ∀ s, ComparisonDomain (fun _ => 0) (u s)) :
    ∃ f : SpinIndex N → WaveSpace (Fin N × Fin 3),
      PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e a.orbital.vector
        a.orbital.positive a.orbital.negative (Metric.ball O (ρ / 2)) u hu f := by
  choose g hg using fun s => (hD (u s)).mpr (hc s)
  let f := PauliMagneticOperatorRealization.source (a.orbital.truncated hρ) C
    (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
    e F χ hUV a.truncatedMagnetic S spectral joint hD a.exponent_gt_two
    a.truncatedMagnetic_memLp u g hg
  have hf := PauliMagneticOperatorRealization.source_pair (a.orbital.truncated hρ) C
    (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
    e F χ hUV a.truncatedMagnetic S spectral joint hD a.exponent_gt_two
    a.truncatedMagnetic_memLp friedrichs KR hG hSA u g hg (truncatedDomain a hρ u hu hs)
  refine ⟨f, ?_⟩
  intro z hz hzs
  have hZ (s : SpinIndex N) := a.orbital.agreement hρ
    (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) (hzs s)
  have hz' : Domain (a.orbital.truncated hρ).vector (a.orbital.truncated hρ).positive
      (a.orbital.truncated hρ).negative z := fun s =>
    domain_congr (fun _ => 0) a.orbital.vector (a.orbital.truncated hρ).vector
      a.orbital.positive a.orbital.negative (a.orbital.truncated hρ).positive
      (a.orbital.truncated hρ).negative (z s) (hz s) (hZ s)
  have huc := fun s => compact_of_ball_support (u s) (hs s)
  have hzc := fun s => compact_of_ball_support (z s) (hzs s)
  have hus := fun n s => coordinate_support_of_ball_support
    (show ρ / 8 ≤ ρ / 2 by linarith only [hρ]) _ (hs s) n
  have hzs' := fun n s => coordinate_support_of_ball_support
    (le_refl (ρ / 2)) _ (hzs s) n
  have hsq := PauliWeakSquare.weak_square_on_balls S spectral joint friedrichs C F χ e hUV W G D
    a.orbital.vectorCoefficient a.magnetic (fun n => (PhysicalSourceCoordinates.split n O).1)
    (fun _ => ρ) (fun _ => hρ) a.exponent a.exponent_gt_two
    a.orbital.vector_memLp a.magnetic_memLp a.weakCurl
    a.orbital.positive a.orbital.negative z u hz hu hzc huc hzs' hus
  have horb : PauliOrbitalForm.form C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
      a.orbital.negative z u hz hu =
    PauliOrbitalForm.form C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (a.orbital.truncated hρ).vector
      (a.orbital.truncated hρ).positive (a.orbital.truncated hρ).negative z u hz'
      (truncatedDomain a hρ u hu hs) := by
    unfold PauliOrbitalForm.form
    exact Finset.sum_congr rfl fun s _ => PhysicalCoefficientLocality.form_congr (fun _ => 0)
      a.orbital.vector (a.orbital.truncated hρ).vector a.orbital.positive a.orbital.negative
      (a.orbital.truncated hρ).positive (a.orbital.truncated hρ).negative
      C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
      (z s) (u s) (hz s) (hu s) (hz' s) (truncatedDomain a hρ u hu hs s)
      (hZ s) (supported_agreement a hρ u hs s)
  have hmag := PauliMagneticCutoffLocality.classical_coefficient_congr a.magnetic a.truncatedMagnetic
    (fun n => Metric.ball (PhysicalSourceCoordinates.split n O).1 (ρ / 2))
    (a.truncatedMagnetic_eq hρ) z u hus
  have hsum := congrArg (fun r : ℂ => r +
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (PauliMagneticOperator.quantum F χ hUV C e u s))
    (congrArg₂ (fun x y : ℂ => x + y) horb hmag)
  exact hsq.trans (hsum.trans (hf z hz'))

include hρ hUV S spectral joint friedrichs W G D KR hD hG hSA in
/-- Local domain equality for the actual weak Pauli form and its
comparison operator, with every multiplier and cutoff condition derived. -/
theorem comparison_domain_iff_local_operatorPair
    (u : Ref N) (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
    (hs : ∀ s, ∀ᵐ X ∂volume, X ∉ Metric.ball O (ρ / 8) →
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X = 0) :
    (∀ s, ComparisonDomain (fun _ => 0) (u s)) ↔
      ∃ f : SpinIndex N → WaveSpace (Fin N × Fin 3),
        PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e a.orbital.vector
          a.orbital.positive a.orbital.negative (Metric.ball O (ρ / 2)) u hu f := by
  constructor
  · exact exists_local_operatorPair_of_comparison_domain a hρ C F χ e S spectral joint
      friedrichs hUV W G D KR hD hG hSA u hu hs
  · rintro ⟨f, hf⟩
    exact comparison_domain_of_local_operatorPair a hρ C F χ e S spectral joint
      friedrichs hUV W G D KR hD hG hSA u hu hs f hf

end PfHk.PauliLocalDomain

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
