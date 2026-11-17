import PfHk.PhysicalOneParticleEnergy
import PfHk.CounterexamplePotentials
import PfHk.CounterexampleSpectral
import PfHk.CounterexamplePairingAlgebra

/-! The zero-coupling magnetic pairing for an arbitrary momentum kernel.
The kernel disappears before the explicit physical profile is specialized. -/

noncomputable section

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.CounterexampleMagneticPairing

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PhysicalOneParticleState

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

local instance photonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

attribute [local irreducible] inclusion covariant ordinary
  PhysicalPFReference.referenceSubspace

private theorem value_electronic (u : Ref) :
    ElectronicH1Complex.value (E := PhotonFock) (I := Index)
        (electronic Index (fun _ => 0) u) =
      inclusion Index (fun _ => 0) u := by
  unfold inclusion
  rfl

private theorem derivative_electronic (u : Ref) (i : Index) :
    ElectronicH1Complex.derivative (E := PhotonFock) (I := Index) i
        (electronic Index (fun _ => 0) u) =
      ordinary Index (fun _ => 0) i u := by
  unfold ordinary
  rfl

private def ordinaryRotation (u : Ref) : ℝ :=
  ∑ j : Fin 3, ∫ X, CounterexampleField.field (SymmetricLift.particle X 0) j *
    (inner ℂ (inclusion Index (fun _ => 0) u X)
      ((-Complex.I) • ordinary Index (fun _ => 0) (0, j) u X)).re

private theorem rotation_eq (u : Ref) :
    CounterexampleSpectral.rotationForm (electronic Index (fun _ => 0) u) =
      ordinaryRotation u := by
  let R (ψ : WaveSpace Index) (d : Fin 3 → WaveSpace Index) : ℝ :=
    ∑ j, ∫ X, CounterexampleField.field (SymmetricLift.particle X 0) j *
      (inner ℂ (ψ X) ((-Complex.I) • d j X)).re
  have hder := funext (fun j : Fin 3 => derivative_electronic u (0, j))
  exact congrArg₂ R (value_electronic u) hder

private theorem covariant_zero {I : Type} [Fintype I] [DecidableEq I]
    (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
    (κ : I → Position I → WeightedPhotonKernel)
    (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hb : ∀ i, ∀ᵐ X ∂volume, ‖κ i X‖ ≤ M)
    (u : Reference I V) (q : I) :
    covariant I V C κ hκ M hb 0 q u = (-Complex.I) • ordinary I V q u :=
  (covariant_apply I V C κ hκ M hb 0 q u).trans
    (by simp only [Complex.ofReal_zero, zero_smul, sub_zero])

private theorem vector_ae (t : ℝ) (j : Fin 3) :
    (fun X : Position Index => PhysicalCommonFormDomain.vector
      (CounterexamplePotentials.vector t) (0, j) X) =ᵐ[volume]
      fun X => t * CounterexampleField.field (SymmetricLift.particle X 0) j :=
  (ScalarCoordinateFormBound.coordinate_ae (N := 1) (0 : Fin 1)
    (CounterexamplePotentials.vector_ae t)).mono fun _X hX =>
      congrArg (fun v : CounterexampleField.Space => v j) hX

variable (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M)

set_option hygiene false in
local notation "κ" => PhysicalPFParticle.particleKernel (N := 1) K
set_option hygiene false in
local notation "hκ" => PhysicalPFParticle.particleKernel_measurable (N := 1) K hK
set_option hygiene false in
local notation "hb" => PhysicalPFParticle.particleKernel_bound (N := 1) K M hM

/-- The explicit magnetic family gives its angular form at zero coupling,
independently of the quantized-field momentum kernel. -/
theorem magneticSum (t : ℝ) (u : Ref) :
    PhysicalShiftedFormEnergy.magneticSum C K hK M hM 0
      (CounterexamplePotentials.vector t) u =
      t * CounterexampleSpectral.rotationForm (electronic Index (fun _ => 0) u) := by
  let f (q : Index) (X : Position Index) : ℝ :=
    PhysicalCommonFormDomain.vector (CounterexamplePotentials.vector t) q X *
      (inner ℂ (inclusion Index (fun _ => 0) u X)
        (covariant Index (fun _ => 0) C κ hκ M hb 0 q u X)).re
  let g (j : Fin 3) (X : Position Index) : ℝ :=
    CounterexampleField.field (SymmetricLift.particle X 0) j *
      (inner ℂ (inclusion Index (fun _ => 0) u X)
        ((-Complex.I) • ordinary Index (fun _ => 0) (0, j) u X)).re
  have hpoint (j : Fin 3) : f (0, j) =ᵐ[volume] fun X => t * g j X := by
    have h := CounterexamplePairingAlgebra.magnetic_pairing_ae
      (Q := Position Index) (μ := volume) (H := PhotonFock)
      (inclusion Index (fun _ => 0) u) (inclusion Index (fun _ => 0) u)
      (ordinary Index (fun _ => 0) (0, j) u) (ordinary Index (fun _ => 0) (0, j) u)
      (covariant Index (fun _ => 0) C κ hκ M hb 0 (0, j) u)
      (fun X => PhysicalCommonFormDomain.vector (CounterexamplePotentials.vector t) (0, j) X)
      (fun X => CounterexampleField.field (SymmetricLift.particle X 0) j) t rfl rfl
      (covariant_zero (fun _ => 0) C κ hκ M hb u (0, j)) (vector_ae t j)
    exact h
  have hs := CounterexamplePairingAlgebra.sum_one (fun q : Index => ∫ X, f q X)
  have hscale := CounterexamplePairingAlgebra.scaled_sum t (fun j => f (0, j)) g hpoint
  exact (hs.trans hscale).trans (congrArg (fun r : ℝ => t * r) (rotation_eq u).symm)

end PfHk.CounterexampleMagneticPairing

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
