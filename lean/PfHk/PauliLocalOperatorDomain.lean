import PfHk.PauliLocalDomainData
import PfHk.PauliLocalOperatorTransfer
import PfHk.PauliMagneticOperatorRealization

/-! The paper's local Lp and weak-divergence/curl hypotheses identify
the Pauli weak operator domain with the finite-spin comparison domain.
All cutoffs and coefficient truncations are constructed here. -/

noncomputable section
namespace PfHk.PauliLocalDomain

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.PauliGroundState PfHk.PauliSpin PfHk.PhysicalLocalEnergy
  PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain PfHk.CenteredPhysicalReference
  PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
  PfHk.FriedrichsDivergenceBackground PfHk.SmoothCutoffBounds
  PfHk.KatoRellichBackground PfHk.PhysicalCoefficientLocality
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion

variable {N : ℕ} {O : Configuration N} {ρ : ℝ}
  (a : Data O ρ) (hρ : 0 < ρ)
  (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff) (e : ℝ)
  (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence)
  (hUV : CarlemanUV χ) (W : ConcreteWeylLaw photonMeasure)
  (G : StandardWeylGraphC1 W) (D : StandardWeylFormCoreDensity W G)

theorem supported_agreement (u : Ref N)
    (hs : ∀ s, ∀ᵐ X ∂volume, X ∉ Metric.ball O (ρ / 8) →
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X = 0) (s : SpinIndex N) :
    Agreement a.orbital.vector (a.orbital.truncated hρ).vector
      a.orbital.positive a.orbital.negative
      (a.orbital.truncated hρ).positive (a.orbital.truncated hρ).negative
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) :=
  a.orbital.agreement hρ _ ((hs s).mono fun X hX hn =>
    hX (fun hx => hn (Metric.mem_ball.mpr
      ((Metric.mem_ball.mp hx).trans_le (by linarith only [hρ])))))

theorem truncatedDomain (u : Ref N) (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
    (hs : ∀ s, ∀ᵐ X ∂volume, X ∉ Metric.ball O (ρ / 8) →
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X = 0) :
    Domain (a.orbital.truncated hρ).vector (a.orbital.truncated hρ).positive
      (a.orbital.truncated hρ).negative u := fun s =>
  domain_congr (fun _ => 0) a.orbital.vector (a.orbital.truncated hρ).vector
    a.orbital.positive a.orbital.negative (a.orbital.truncated hρ).positive
    (a.orbital.truncated hρ).negative (u s) (hu s) (supported_agreement a hρ u hs s)

include S spectral joint friedrichs W G D in
theorem truncated_operatorPair (family : BufferedFamily O)
    (u : Ref N) (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
    (hs : ∀ s, ∀ᵐ X ∂volume, X ∉ Metric.ball O (ρ / 8) →
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X = 0)
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hf : PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e
      a.orbital.vector a.orbital.positive a.orbital.negative (Metric.ball O (ρ / 2)) u hu f) :
    PauliMagneticOperatorRealization.IsOperatorPair (a.orbital.truncated hρ) C
      (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
      e F χ hUV a.truncatedMagnetic u (truncatedDomain a hρ u hu hs)
      (fun s => (family.cutoff (ρ / 8)).scalar.multiplier (f s)) := by
  have ht : 0 < ρ / 8 := by positivity
  have hsupport (X : Configuration N) (hn : X ∉ Metric.ball O (ρ / 2)) :
      (family.cutoff (ρ / 8)).scalar.weight X = 0 :=
    BufferedCutoffLocality.cutoff_supported family ht X
      (fun hx => hn (Metric.mem_ball.mpr
        ((Metric.mem_ball.mp hx).trans_le (by linarith only [hρ]))))
  have hinside (X : Configuration N)
      (hn : (family.cutoff (ρ / 8)).scalar.weight X ≠ 0) : X ∈ Metric.ball O (ρ / 2) :=
    Classical.byContradiction fun hout => hn (hsupport X hout)
  have hact (s : SpinIndex N) := BufferedCutoffLocality.cutoff_action family ht
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hs s)
  exact PauliLocalOperatorTransfer.operatorPair_of_local C F χ e S spectral joint friedrichs
    hUV W G D a.orbital.vectorCoefficient a.magnetic a.truncatedMagnetic
    (fun n => (PhysicalSourceCoordinates.split n O).1) (fun _ => ρ) (fun _ => hρ)
    a.exponent a.exponent_gt_two a.orbital.vector_memLp a.magnetic_memLp a.weakCurl
    a.orbital.positive a.orbital.negative (a.orbital.truncated hρ)
    (family.cutoff (ρ / 8)) hsupport
    (fun i X hX => (a.orbital.truncated_vector_eq hρ i (hinside X hX)).symm)
    (fun X hX => (a.orbital.truncated_positive_eq hρ (hinside X hX)).symm)
    (fun X hX => (a.orbital.truncated_negative_eq hρ (hinside X hX)).symm)
    (a.truncatedMagnetic_eq hρ) u hu (truncatedDomain a hρ u hu hs)
    (supported_agreement a hρ u hs) (fun s => (hact s).1)
    (fun i s => (hact s).2.1 i) (fun i s => (hact s).2.2 i)
    (fun s => compact_of_ball_support (u s) (hs s))
    (fun n s => coordinate_support_of_ball_support (by linarith only [hρ]) _ (hs s) n)
    (localized_compact family ht)
    (fun z n s => localized_coordinate_support family ht (by linarith only [hρ]) z n s) f hf

variable (KR : StandardKatoRellich)
  (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hSA : SelfAdjointGraph (PhysicalExternalOperator.freeHilbertGraph (fun _ => 0) C
    (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e))

include hρ hUV S spectral joint friedrichs W G D KR hD hG hSA in
/-- A compactly supported local Pauli operator vector belongs to the
actual comparison domain under the paper's coefficient assumptions. -/
theorem comparison_domain_of_local_operatorPair
    (u : Ref N) (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
    (hs : ∀ s, ∀ᵐ X ∂volume, X ∉ Metric.ball O (ρ / 8) →
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X = 0)
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hf : PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e
      a.orbital.vector a.orbital.positive a.orbital.negative (Metric.ball O (ρ / 2)) u hu f) :
    ∀ s, ComparisonDomain (fun _ => 0) (u s) := by
  let family : BufferedFamily O := Classical.choice (exists_buffered_family O)
  have hpair := truncated_operatorPair a hρ C F χ e S spectral joint friedrichs hUV W G D
    family u hu hs f hf
  exact PauliMagneticOperatorRealization.operatorPair_comparison_domain
    (a.orbital.truncated hρ) C (profile F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e F χ hUV a.truncatedMagnetic
    S spectral joint hD a.exponent_gt_two a.truncatedMagnetic_memLp friedrichs KR hG hSA
    u (truncatedDomain a hρ u hu hs) _ hpair

end PfHk.PauliLocalDomain

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
