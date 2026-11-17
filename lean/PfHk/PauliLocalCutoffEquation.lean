import PfHk.PauliLocalCutoffRules
import PfHk.PauliLocalDomainData
import PfHk.PauliMagneticCutoffLocality
import PfHk.PauliLocalOperatorTransfer

/-! The exact cutoff equation for a physical Pauli weak eigenstate.
Two compact weak-square identities reduce the computation to the
already proved orbital commutator. The magnetic forms cancel through
real scalar cutoffs. -/

noncomputable section
namespace PfHk.PauliLocalCutoffEquation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  GptLean.ElectronicH1Multiplier PfHk.PauliSpin PfHk.PauliGroundState
  PfHk.PauliLocalEnergy PfHk.PhysicalLocalEnergy PfHk.PhysicalFieldRegularity
  PfHk.CenteredPhysicalReference
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
  PfHk.FriedrichsDivergenceBackground PfHk.SmoothCutoffBounds
  PfHk.PhysicalCutoffCommutator PfHk.PauliLocalCutoffRules
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion rawForm PauliOrbitalForm.form
  PauliSquareForm.classicalForm PauliMagneticOperator.quantum PhysicalPFScalarMultiplier.multiply
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier
  PauliLocalEnergy.localize

variable {N : ℕ}

private theorem classical_two_cutoffs
    (η ζ : DifferentiableMultiplier (Fin N × Fin 3))
    (B : Fin N → Fin 3 → PhysicalSourceCoordinates.Position → ℝ) (z u : Ref N)
    (hz : localize ζ (localize η z) = localize η z)
    (hu : localize ζ (localize η u) = localize η u) :
    PauliSquareForm.classicalForm B (localize ζ z) (localize η u) =
      PauliSquareForm.classicalForm B (localize η z) (localize ζ u) := by
  have hl := (PauliMagneticCutoffLocality.classical_cutoff_pairing ζ B z (localize η u)).trans
    (congrArg (PauliSquareForm.classicalForm B z) hu)
  have hr := (PauliMagneticCutoffLocality.classical_cutoff_pairing ζ B (localize η z) u).symm.trans
    ((congrArg (fun w : Ref N => PauliSquareForm.classicalForm B w u) hz).trans
      (PauliMagneticCutoffLocality.classical_cutoff_pairing η B z u))
  exact hl.trans hr.symm

def quantumPair (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
    (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (z u : Ref N) : ℂ :=
  ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
    (PauliMagneticOperator.quantum F χ hUV C e u s)

private theorem quantum_two_cutoffs (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
    (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (η ζ : DifferentiableMultiplier (Fin N × Fin 3)) (z u : Ref N)
    (hz : localize ζ (localize η z) = localize η z)
    (hu : localize ζ (localize η u) = localize η u) :
    quantumPair F χ hUV C e (localize ζ z) (localize η u) =
      quantumPair F χ hUV C e (localize η z) (localize ζ u) := by
  have hl : quantumPair F χ hUV C e (localize ζ z) (localize η u) =
      quantumPair F χ hUV C e z (localize η u) :=
    (PauliMagneticCutoffLocality.quantum_cutoff_pairing F χ hUV C e ζ z (localize η u)).trans
      (congrArg (quantumPair F χ hUV C e z) hu)
  have hr : quantumPair F χ hUV C e (localize η z) (localize ζ u) =
      quantumPair F χ hUV C e z (localize η u) :=
    (PauliMagneticCutoffLocality.quantum_cutoff_pairing F χ hUV C e ζ (localize η z) u).symm.trans
      ((congrArg (fun w : Ref N => quantumPair F χ hUV C e w u) hz).trans
        (PauliMagneticCutoffLocality.quantum_cutoff_pairing F χ hUV C e η z u))
  exact hl.trans hr.symm

variable {O : Configuration N} {ρ : ℝ}
  (a : PauliLocalDomain.Data O ρ) (hρ : 0 < ρ)
  (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff) (e : ℝ)
  (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence)
  (hUV : CarlemanUV χ) (W : ConcreteWeylLaw photonMeasure)
  (G : StandardWeylGraphC1 W) (D : StandardWeylFormCoreDensity W G)

include hρ S spectral joint friedrichs hUV W G D in
theorem form_commutator (family : BufferedFamily O) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ / 32)
    (z u : Ref N) (hz : Domain a.orbital.vector a.orbital.positive a.orbital.negative z)
    (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u) :
    rawForm C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
      (profile_bound F χ 0) e a.orbital.vector a.orbital.positive a.orbital.negative
      z (localize (family.cutoff r).scalar u) hz (domain_localize hu (family.cutoff r).scalar) =
    rawForm C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
      (profile_bound F χ 0) e a.orbital.vector a.orbital.positive a.orbital.negative
      (localize (family.cutoff r).scalar z) u (domain_localize hz (family.cutoff r).scalar) hu +
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (PauliLocalCutoffRules.commutator C (profile F χ 0) (profile_measurable F χ 0)
          (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
          a.orbital.negative (family.cutoff r) u hu s) := by
  let η := family.cutoff r
  let ζ := family.cutoff (ρ / 4)
  have hζ : 0 < ρ / 4 := by positivity
  have houter : 2 * r ≤ ρ / 4 := by linarith only [hrρ, hρ]
  have hinner : 2 * r ≤ ρ / 2 := by linarith only [hrρ, hρ]
  have hact (w : Ref N) (s : SpinIndex N) :=
    PauliBufferedCutoffLocality.cutoff_action_mixed family hζ
      (inclusion (Fin N × Fin 3) (fun _ => 0) (localize η.scalar w s))
      (localized_supported_radius family hr houter w s)
  have hfixed (w : Ref N) : localize ζ.scalar (localize η.scalar w) = localize η.scalar w := by
    funext s
    simpa only [localize] using
      PauliFlatCutoff.reference_fixed ζ (localize η.scalar w) (fun t => (hact w t).1) s
  have hrawL := PauliFlatCutoff.rawForm_localize_left C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
    a.orbital.vector a.orbital.positive a.orbital.negative ζ z (localize η.scalar u)
    hz (domain_localize hu η.scalar) (fun s => (hact u s).1)
    (fun i s => (hact u s).2.1 i) (fun i j s => (hact u s).2.2 i j)
  have hrawR := rawForm_localize_right C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
    a.orbital.vector a.orbital.positive a.orbital.negative ζ (localize η.scalar z) u
    (domain_localize hz η.scalar) hu (fun s => (hact z s).1)
    (fun i s => (hact z s).2.1 i) (fun i j s => (hact z s).2.2 i j)
  have horbL := PauliOrbitalCutoffLocality.form_localize_left C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
    a.orbital.vector a.orbital.positive a.orbital.negative ζ z (localize η.scalar u)
    hz (domain_localize hu η.scalar) (fun s => (hact u s).1)
    (fun i s => (hact u s).2.1 i) (fun i s => (hact u s).2.2 i i)
  have horbR := orbitalForm_localize_right C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
    a.orbital.vector a.orbital.positive a.orbital.negative ζ (localize η.scalar z) u
    (domain_localize hz η.scalar) hu (fun s => (hact z s).1)
    (fun i s => (hact z s).2.1 i) (fun i s => (hact z s).2.2 i i)
  have hsL := PauliWeakSquare.weak_square_on_balls S spectral joint friedrichs C F χ e hUV W G D
    a.orbital.vectorCoefficient a.magnetic (fun n => (PhysicalSourceCoordinates.split n O).1)
    (fun _ => ρ) (fun _ => hρ) a.exponent a.exponent_gt_two a.orbital.vector_memLp
    a.magnetic_memLp a.weakCurl a.orbital.positive a.orbital.negative
    (localize ζ.scalar z) (localize η.scalar u) (domain_localize hz ζ.scalar) (domain_localize hu η.scalar)
    (PauliLocalDomain.localized_compact family hζ z) (PauliLocalDomain.localized_compact family hr u)
    (PauliLocalDomain.localized_coordinate_support (R := ρ / 2) family hζ (by linarith only) z)
    (PauliLocalDomain.localized_coordinate_support (R := ρ / 2) family hr hinner u)
  have hsR := PauliWeakSquare.weak_square_on_balls S spectral joint friedrichs C F χ e hUV W G D
    a.orbital.vectorCoefficient a.magnetic (fun n => (PhysicalSourceCoordinates.split n O).1)
    (fun _ => ρ) (fun _ => hρ) a.exponent a.exponent_gt_two a.orbital.vector_memLp
    a.magnetic_memLp a.weakCurl a.orbital.positive a.orbital.negative
    (localize η.scalar z) (localize ζ.scalar u) (domain_localize hz η.scalar) (domain_localize hu ζ.scalar)
    (PauliLocalDomain.localized_compact family hr z) (PauliLocalDomain.localized_compact family hζ u)
    (PauliLocalDomain.localized_coordinate_support (R := ρ / 2) family hr hinner z)
    (PauliLocalDomain.localized_coordinate_support (R := ρ / 2) family hζ (by linarith only) u)
  have hL := hrawL.symm.trans (hsL.trans (congrArg
    (fun t : ℂ => t + PauliSquareForm.classicalForm a.magnetic (localize ζ.scalar z) (localize η.scalar u) +
      quantumPair F χ hUV C e (localize ζ.scalar z) (localize η.scalar u)) horbL))
  have hR := hrawR.symm.trans (hsR.trans (congrArg
    (fun t : ℂ => t + PauliSquareForm.classicalForm a.magnetic (localize η.scalar z) (localize ζ.scalar u) +
      quantumPair F χ hUV C e (localize η.scalar z) (localize ζ.scalar u)) horbR))
  exact magnetic_cancel hL hR
    (classical_two_cutoffs η.scalar ζ.scalar a.magnetic z u (hfixed z) (hfixed u))
    (quantum_two_cutoffs F χ hUV C e η.scalar ζ.scalar z u (hfixed z) (hfixed u))
    (orbital_form_commutator C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
      a.orbital.negative η z u hz hu)

def source (η : TwiceDifferentiableMultiplier (Fin N × Fin 3)) (E : ℝ)
    (u : Ref N) (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u) :
    SpinIndex N → WaveSpace (Fin N × Fin 3) :=
  fun s => (E : ℂ) • η.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) +
    PauliLocalCutoffRules.commutator C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
      a.orbital.negative η u hu s

theorem source_pairing (η : TwiceDifferentiableMultiplier (Fin N × Fin 3)) (E : ℝ)
    (z u : Ref N) (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u) :
    (∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) (source a C F χ e η E u hu s)) =
      (E : ℂ) * mass (N := N) z (localize η.scalar u) +
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (PauliLocalCutoffRules.commutator C (profile F χ 0) (profile_measurable F χ 0)
          (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
          a.orbital.negative η u hu s) := by
  have hm : mass (N := N) z (localize η.scalar u) =
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (η.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))) := by
    unfold mass localize
    exact Finset.sum_congr rfl fun s _ => congrArg
      (inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)))
      (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) η.scalar (u s))
  have h := eigen_source_pairing (E : ℂ)
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
    (fun s => η.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))
    (PauliLocalCutoffRules.commutator C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
      a.orbital.negative η u hu)
  exact h.trans (congrArg (fun t : ℂ => (E : ℂ) * t +
    ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (PauliLocalCutoffRules.commutator C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
        a.orbital.negative η u hu s)) hm.symm)

include hρ S spectral joint friedrichs hUV W G D in
theorem eigenstate_localized_equation (family : BufferedFamily O) {r : ℝ}
    (hr : 0 < r) (hrρ : r ≤ ρ / 32) (E : ℝ) (u : Ref N)
    (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
      a.orbital.negative E u hu)
    (z : Ref N) (hz : Domain a.orbital.vector a.orbital.positive a.orbital.negative z) :
    rawForm C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
      (profile_bound F χ 0) e a.orbital.vector a.orbital.positive a.orbital.negative
      z (localize (family.cutoff r).scalar u) hz (domain_localize hu (family.cutoff r).scalar) =
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (source a C F χ e (family.cutoff r) E u hu s) := by
  have h := form_commutator a hρ C F χ e S spectral joint friedrichs hUV W G D
    family hr hrρ z u hz hu
  have he := (heigen (localize (family.cutoff r).scalar z)
    (domain_localize hz (family.cutoff r).scalar)).trans
    (congrArg (fun t : ℂ => (E : ℂ) * t) (mass_cutoff_pairing (family.cutoff r).scalar z u))
  exact h.trans ((congrArg (fun t : ℂ => t +
    ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (PauliLocalCutoffRules.commutator C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
        a.orbital.negative (family.cutoff r) u hu s)) he).trans
    (source_pairing a C F χ e (family.cutoff r) E z u hu).symm)

include hρ S spectral joint friedrichs hUV W G D in
theorem eigenstate_local_operatorPair (family : BufferedFamily O) {r : ℝ}
    (hr : 0 < r) (hrρ : r ≤ ρ / 32) (E : ℝ) (u : Ref N)
    (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
      a.orbital.negative E u hu) :
    PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e a.orbital.vector
      a.orbital.positive a.orbital.negative (Metric.ball O (ρ / 2))
      (localize (family.cutoff r).scalar u) (domain_localize hu (family.cutoff r).scalar)
      (source a C F χ e (family.cutoff r) E u hu) := by
  intro z hz _
  exact eigenstate_localized_equation a hρ C F χ e S spectral joint friedrichs hUV W G D
    family hr hrρ E u hu heigen z hz

end PfHk.PauliLocalCutoffEquation
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
