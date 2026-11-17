import PfHk.PauliLocalCutoffEquation

/-! The exact Pauli cutoff equation for any smooth scalar cutoff
supported in an inner coefficient ball. This includes annular differences
centered at nearby configurations. The classical curl stays a form
throughout the compact weak-square argument. -/

noncomputable section
namespace PfHk.PauliSupportedCutoffEquation

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
theorem form_commutator (family : BufferedFamily O)
    (η : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (hη : ∀ X, X ∉ Metric.ball O (ρ / 4) → η.scalar.weight X = 0)
    (z u : Ref N) (hz : Domain a.orbital.vector a.orbital.positive a.orbital.negative z)
    (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u) :
    rawForm C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
      (profile_bound F χ 0) e a.orbital.vector a.orbital.positive a.orbital.negative
      z (localize η.scalar u) hz (domain_localize hu η.scalar) =
    rawForm C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
      (profile_bound F χ 0) e a.orbital.vector a.orbital.positive a.orbital.negative
      (localize η.scalar z) u (domain_localize hz η.scalar) hu +
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (PauliLocalCutoffRules.commutator C (profile F χ 0) (profile_measurable F χ 0)
          (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
          a.orbital.negative η u hu s) := by
  let ζ := family.cutoff (ρ / 4)
  have hζ : 0 < ρ / 4 := by positivity
  have hsupp (w : Ref N) (s : SpinIndex N) :
      ∀ᵐ X ∂volume, X ∉ Metric.ball O (ρ / 4) →
        inclusion (Fin N × Fin 3) (fun _ => 0) (localize η.scalar w s) X = 0 := by
    unfold localize
    exact localized_supported (fun _ => 0) η.scalar hη (w s)
  have hcompact (w : Ref N) (s : SpinIndex N) :=
    PauliLocalDomain.compact_of_ball_support (localize η.scalar w s) (hsupp w s)
  have hcoordinate (w : Ref N) (n : Fin N) (s : SpinIndex N) :=
    PauliLocalDomain.coordinate_support_of_ball_support
      (by linarith only [hρ] : ρ / 4 ≤ ρ / 2)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (localize η.scalar w s)) (hsupp w s) n
  have hact (w : Ref N) (s : SpinIndex N) :=
    PauliBufferedCutoffLocality.cutoff_action_mixed family hζ
      (inclusion (Fin N × Fin 3) (fun _ => 0) (localize η.scalar w s))
      (hsupp w s)
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
    (PauliLocalDomain.localized_compact family hζ z) (hcompact u)
    (PauliLocalDomain.localized_coordinate_support (R := ρ / 2) family hζ (by linarith only) z)
    (hcoordinate u)
  have hsR := PauliWeakSquare.weak_square_on_balls S spectral joint friedrichs C F χ e hUV W G D
    a.orbital.vectorCoefficient a.magnetic (fun n => (PhysicalSourceCoordinates.split n O).1)
    (fun _ => ρ) (fun _ => hρ) a.exponent a.exponent_gt_two a.orbital.vector_memLp
    a.magnetic_memLp a.weakCurl a.orbital.positive a.orbital.negative
    (localize η.scalar z) (localize ζ.scalar u) (domain_localize hz η.scalar) (domain_localize hu ζ.scalar)
    (hcompact z) (PauliLocalDomain.localized_compact family hζ u)
    (hcoordinate z)
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

include hρ S spectral joint friedrichs hUV W G D in
/-- Every supported smooth cutoff has the actual commutator source,
with the energy term acting on the localized Pauli spinor. -/
theorem eigenstate_local_operatorPair
    (η : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (hη : ∀ X, X ∉ Metric.ball O (ρ / 4) → η.scalar.weight X = 0)
    (E : ℝ) (u : Ref N)
    (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
      a.orbital.negative E u hu) (U : Set (Configuration N)) :
    PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e a.orbital.vector
      a.orbital.positive a.orbital.negative U (localize η.scalar u)
      (domain_localize hu η.scalar)
      (fun s => PauliLocalCutoffRules.commutator C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
        a.orbital.vector a.orbital.positive a.orbital.negative η u hu s +
        (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (localize η.scalar u s)) := by
  let family := Classical.choice (exists_buffered_family O)
  intro z hz _
  have h := form_commutator a hρ C F χ e S spectral joint friedrichs hUV W G D
    family η hη z u hz hu
  have he := (heigen (localize η.scalar z) (domain_localize hz η.scalar)).trans
    (congrArg (fun t : ℂ => (E : ℂ) * t) (mass_cutoff_pairing η.scalar z u))
  have hsource := h.trans ((congrArg (fun t : ℂ => t +
    ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (PauliLocalCutoffRules.commutator C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
        a.orbital.negative η u hu s)) he).trans
    (PauliLocalCutoffEquation.source_pairing a C F χ e η E z u hu).symm)
  refine hsource.trans (Finset.sum_congr rfl fun s _ => congrArg
    (inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))) ?_)
  have hv : inclusion (Fin N × Fin 3) (fun _ => 0) (localize η.scalar u s) =
      η.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) := by
    unfold localize
    exact PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) η.scalar (u s)
  exact (congrArg (fun w : WaveSpace (Fin N × Fin 3) => (E : ℂ) • w +
    PauliLocalCutoffRules.commutator C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e a.orbital.vector a.orbital.positive
      a.orbital.negative η u hu s) hv.symm).trans (add_comm _ _)

end PfHk.PauliSupportedCutoffEquation
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
