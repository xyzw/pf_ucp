import PfHk.PhysicalOneParticleEnergy
import PfHk.CounterexamplePotentials
import PfHk.CounterexampleSpectral
import PfHk.CounterexampleEnergyAlgebra
import PfHk.CounterexamplePairingAlgebra
import PfHk.CounterexampleMagneticPairing

/-! Identification of the actual physical shifted energy with the
electronic angular-channel form and the radiation energy. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.CounterexamplePhysicalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms
  PfHk.PhysicalOneParticleState
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

local instance physicalEnergyPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  CounterexampleMagneticPairing.photonRealInner

attribute [local irreducible] inclusion covariant ordinary radiation
  PhysicalPFReference.referenceSubspace

theorem value_electronic (u : Ref) :
    ElectronicH1Complex.value (E := PhotonFock) (I := Index) (electronic Index (fun _ => 0) u) =
      inclusion Index (fun _ => 0) u := by
  unfold inclusion
  rfl

theorem derivative_electronic (u : Ref) (i : Index) :
    ElectronicH1Complex.derivative (E := PhotonFock) (I := Index) i (electronic Index (fun _ => 0) u) =
      ordinary Index (fun _ => 0) i u := by
  unfold ordinary
  rfl

theorem scalarSum (Z : ℝ) (u : Ref) :
    PhysicalShiftedFormEnergy.scalarSum (CounterexamplePotentials.coulomb Z) u =
      -Z * CounterexampleSpectral.coulomb (electronic Index (fun _ => 0) u) := by
  unfold PhysicalShiftedFormEnergy.scalarSum
  simp only [Fintype.sum_unique]
  change (∫ X, (CounterexamplePotentials.coulomb Z).val (SymmetricLift.particle X 0) *
    ‖inclusion Index (fun _ => 0) u X‖ ^ 2) = _
  have hs := CounterexamplePairingAlgebra.scalar_integral Z
    (fun X => (CounterexamplePotentials.coulomb Z).val (SymmetricLift.particle X 0))
    (fun X => ‖inclusion Index (fun _ => 0) u X‖ ^ 2)
    (fun X => ‖SymmetricLift.particle X 0‖)
    (ScalarCoordinateFormBound.coordinate_ae (N := 1) (0 : Fin 1)
      (CounterexamplePotentials.coulomb_ae Z))
  have hc : CounterexampleSpectral.coulomb (electronic Index (fun _ => 0) u) =
      ∫ X, ‖inclusion Index (fun _ => 0) u X‖ ^ 2 / ‖SymmetricLift.particle X 0‖ :=
    congrArg (fun ψ : WaveSpace Index =>
      ∫ X, ‖ψ X‖ ^ 2 / ‖SymmetricLift.particle X 0‖) (value_electronic u)
  exact hs.trans (congrArg (fun r : ℝ => -Z * r) hc.symm)

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)

set_option hygiene false in
local notation "Kf" => PhysicalProfiles.momentumKernel (formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "hKf" => PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "MK" => PhysicalRemovalKernels.bound F χ
set_option hygiene false in
local notation "hMK" => PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := 1) Kf
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := 1) Kf hKf
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := 1) Kf MK hMK

theorem magneticSum (t : ℝ) (u : Ref) :
    PhysicalShiftedFormEnergy.magneticSum C Kf hKf MK hMK 0
      (CounterexamplePotentials.vector t) u =
      t * CounterexampleSpectral.rotationForm (electronic Index (fun _ => 0) u) :=
  CounterexampleMagneticPairing.magneticSum C Kf hKf MK hMK t u

variable (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

/-- The exact physical Hamiltonian decomposition after scalar cancellation.
It holds for every normalized state in the original model, not only for
the proposed ground state. -/
theorem shiftedEnergy (Z t : ℝ) (p : State F χ C B S 0 (N := 1)) (u : Ref)
    (hu : inclusion Index (fun _ => 0) u = p.val) :
    PhysicalGroundState.shiftedEnergy (0 : Fin 1) F χ C B S 0
      (PhysicalDiamagneticPotential.shifted (CounterexamplePotentials.scalar Z t)
        (CounterexamplePotentials.vector t)) p =
      CounterexampleSpectral.electronicEnergy Z t (electronic Index (fun _ => 0) u) +
        ‖radiation Index (fun _ => 0) u‖ ^ 2 := by
  have hshift := congrArg (fun a =>
    PhysicalGroundState.shiftedEnergy (0 : Fin 1) F χ C B S 0 a p)
    (CounterexamplePotentials.shifted_eq Z t)
  have he := PhysicalOneParticleEnergy.shiftedEnergy F χ C B S
    (CounterexamplePotentials.coulomb Z) (CounterexamplePotentials.vector t) p u hu
  have hp := congrArg₂ (fun s m : ℝ =>
    (1 / 2 : ℝ) * (∑ q : Index, ‖ordinary Index (fun _ => 0) q u‖ ^ 2) +
      ‖radiation Index (fun _ => 0) u‖ ^ 2 + s + m)
    (scalarSum Z u) (magneticSum F χ C t u)
  have hk : CounterexampleSpectral.kinetic (electronic Index (fun _ => 0) u) =
      (1 / 2 : ℝ) * ∑ q : Index, ‖ordinary Index (fun _ => 0) q u‖ ^ 2 :=
    congrArg (fun d : Index → WaveSpace Index => (1 / 2 : ℝ) * ∑ q, ‖d q‖ ^ 2)
      (funext (fun q : Index => derivative_electronic u q))
  have hr :
      ((1 / 2 : ℝ) * ∑ q : Index, ‖ordinary Index (fun _ => 0) q u‖ ^ 2) -
          Z * CounterexampleSpectral.coulomb (electronic Index (fun _ => 0) u) +
          t * CounterexampleSpectral.rotationForm (electronic Index (fun _ => 0) u) +
          ‖radiation Index (fun _ => 0) u‖ ^ 2 =
        CounterexampleSpectral.electronicEnergy Z t (electronic Index (fun _ => 0) u) +
          ‖radiation Index (fun _ => 0) u‖ ^ 2 :=
    congrArg (fun k : ℝ =>
      k - Z * CounterexampleSpectral.coulomb (electronic Index (fun _ => 0) u) +
        t * CounterexampleSpectral.rotationForm (electronic Index (fun _ => 0) u) +
        ‖radiation Index (fun _ => 0) u‖ ^ 2) hk.symm
  have haccount := CounterexampleEnergyAlgebra.regroup
    ((1 / 2 : ℝ) * ∑ q : Index, ‖ordinary Index (fun _ => 0) q u‖ ^ 2)
    (‖radiation Index (fun _ => 0) u‖ ^ 2) Z
    (CounterexampleSpectral.coulomb (electronic Index (fun _ => 0) u)) t
    (CounterexampleSpectral.rotationForm (electronic Index (fun _ => 0) u))
  exact hshift.trans (he.trans (hp.trans (haccount.trans hr)))

end PfHk.CounterexamplePhysicalEnergy

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
