import PfHk.PhysicalZeroCouplingDerivative
import GptLean.PhysicalSourcePair

/-! The actual one-electron density and current have no spectator integral.
These identities connect explicit wave functions to the model's Pair. -/

noncomputable section

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PhysicalOneParticleData

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms
  GptLean.PhysicalPairSpace PfHk.PhysicalOneParticleState
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

local instance dataPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

attribute [local irreducible] inclusion covariant ordinary PhysicalPFReference.referenceSubspace

local instance remaining_empty : IsEmpty (PhysicalSourceCoordinates.Remaining (0 : Fin 1)) :=
  ⟨fun j => j.1.property (Subsingleton.elim _ _)⟩

def configuration (x : Gaussian.FieldSpace) : PhysicalPFReference.Position Index :=
  (PhysicalSourceCoordinates.split (0 : Fin 1)).symm (x, 0)

theorem configuration_particle (x : Gaussian.FieldSpace) :
    SymmetricLift.particle (configuration x) (0 : Fin 1) = x := by
  have h := congrArg Prod.fst
    ((PhysicalSourceCoordinates.split (0 : Fin 1)).apply_symm_apply (x, 0))
  exact h

/-- Pull back an almost-everywhere identity along the one-particle
configuration identification. The spectator space has its unit point mass. -/
theorem ae_configuration {P : PhysicalPFReference.Position Index → Prop}
    (hP : ∀ᵐ X ∂volume, P X) : ∀ᵐ x ∂volume, P (configuration x) := by
  have hp := (PhysicalSourceCoordinates.split_symm_measurePreserving
    (0 : Fin 1)).quasiMeasurePreserving.ae hP
  have hs := Measure.ae_ae_of_ae_prod hp
  filter_upwards [hs] with x hx
  simpa [volume_euclideanSpace_eq_dirac, ae_dirac_eq, configuration] using hx

private theorem source_density {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ElectronicH1Space.H1 H Index)
    (d : Fin 3 → ElectronicH1Space.L2 H Index) :
    densityL1 (PhysicalSourcePair.ofWaveFunction (0 : Fin 1) u d) =ᵐ[volume]
      fun x => ‖ElectronicH1Space.value u (configuration x)‖ ^ 2 := by
  have hd := PhysicalSourcePair.density_ofWaveFunction_ae (0 : Fin 1) u d
  filter_upwards [hd] with x hx
  simpa only [volume_euclideanSpace_eq_dirac, integral_dirac,
    Nat.cast_one, one_mul, configuration] using hx

private theorem source_current {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ElectronicH1Space.H1 H Index)
    (d : Fin 3 → ElectronicH1Space.L2 H Index) (j : Fin 3) :
    (fun x => currentL1 (PhysicalSourcePair.ofWaveFunction (0 : Fin 1) u d) x j) =ᵐ[volume]
      fun x => (⟪ElectronicH1Space.value u (configuration x), d j (configuration x)⟫_ℂ).re := by
  have hd := PhysicalSourcePair.current_ofWaveFunction_ae (0 : Fin 1) u d j
  filter_upwards [hd] with x hx
  simpa only [volume_euclideanSpace_eq_dirac, integral_dirac,
    Nat.cast_one, one_mul, configuration] using hx

private theorem density_from_source {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (D : Pair) (u : ElectronicH1Space.H1 H Index)
    (d : Fin 3 → ElectronicH1Space.L2 H Index) (ψ : ElectronicH1Space.L2 H Index)
    (hD : D = PhysicalSourcePair.ofWaveFunction (0 : Fin 1) u d)
    (hψ : ElectronicH1Space.value u = ψ) :
    densityL1 D =ᵐ[volume] fun x => ‖ψ (configuration x)‖ ^ 2 := by
  subst D ψ
  exact source_density u d

private theorem current_from_source {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (D : Pair) (u : ElectronicH1Space.H1 H Index)
    (d : Fin 3 → ElectronicH1Space.L2 H Index) (ψ : ElectronicH1Space.L2 H Index)
    (m : Fin 3 → Position Index → H)
    (hD : D = PhysicalSourcePair.ofWaveFunction (0 : Fin 1) u d)
    (hψ : ElectronicH1Space.value u = ψ)
    (hd : ∀ j, d j =ᵐ[volume] m j)
    (hj : ∀ j, ∀ᵐ X ∂volume, (⟪ψ X, m j X⟫_ℂ).re = 0) :
    currentL1 D =ᵐ[volume] 0 := by
  subst D ψ
  have hc (j : Fin 3) : ∀ᵐ x ∂volume,
      currentL1 (PhysicalSourcePair.ofWaveFunction (0 : Fin 1) u d) x j = 0 := by
    filter_upwards [source_current u d j, ae_configuration (hd j),
      ae_configuration (hj j)] with x hx hdj hjx
    exact hx.trans ((congrArg (fun z : H =>
      (⟪ElectronicH1Space.value u (configuration x), z⟫_ℂ).re) hdj).trans hjx)
  filter_upwards [ae_all_iff.mpr hc] with x hx
  ext j
  exact hx j

private theorem coe_eq_smul {X H : Type*} [MeasurableSpace X]
    (μ : Measure X) [NormedAddCommGroup H] [NormedSpace ℂ H]
    (c : ℂ) (u v : Lp H 2 μ) (h : u = c • v) :
    u =ᵐ[μ] fun x => c • v x := by
  subst u
  exact Lp.coeFn_smul c v

private theorem reference_value (u : Ref) :
    ElectronicH1Complex.value (electronic Index (fun _ => 0) u) =
      inclusion Index (fun _ => 0) u := by
  unfold inclusion
  rfl

variable (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground)

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

/-- The density component of the actual one-particle Pair is the wave
function's squared norm in the corresponding configuration. -/
theorem density (e : ℝ) (p : State F χ C B S e (N := 1)) :
    densityL1 ((model (0 : Fin 1) F χ C B S e).density p) =ᵐ[volume]
      fun x => ‖p.val (configuration x)‖ ^ 2 := by
  let u := PhysicalGroundStateWeak.stateReference F χ C B S e p
  have hu := PhysicalGroundStateWeak.stateReference_value F χ C B S e p
  have hp := PhysicalGroundStateWeak.pure_density_eq_pair F χ C B S e
    (0 : Fin 1) p u hu
  have he := (ElectronicH1Complex.value_realEquiv (electronic Index (fun _ => 0) u)).trans
    ((reference_value u).trans hu)
  exact density_from_source (H := PhotonFock) _
    (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Index) (electronic Index (fun _ => 0) u))
    (fun j => covariant Index (fun _ => 0) C κP hκP MK hbP e (0, j) u)
    p.val hp he

/-- Vanishing of all pointwise momentum-current components gives zero
combined current in the actual one-electron model at zero coupling. -/
theorem current_zero (p : State F χ C B S 0 (N := 1)) (u : Ref)
    (hu : inclusion Index (fun _ => 0) u = p.val)
    (hj : ∀ j : Fin 3, ∀ᵐ X ∂volume,
      (⟪inclusion Index (fun _ => 0) u X,
        (-Complex.I) • ordinary Index (fun _ => 0) (0, j) u X⟫_ℂ).re = 0) :
    currentL1 ((model (0 : Fin 1) F χ C B S 0).density p) =ᵐ[volume] 0 := by
  have hp := PhysicalGroundStateWeak.pure_density_eq_pair F χ C B S 0
    (0 : Fin 1) p u hu
  have he := (ElectronicH1Complex.value_realEquiv (electronic Index (fun _ => 0) u)).trans
    (reference_value u)
  exact current_from_source (H := PhotonFock) _
    (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Index) (electronic Index (fun _ => 0) u))
    (fun j => covariant Index (fun _ => 0) C κP hκP MK hbP 0 (0, j) u)
    (inclusion Index (fun _ => 0) u)
    (fun j X => (-Complex.I) • ordinary Index (fun _ => 0) (0, j) u X)
    hp he (fun j => coe_eq_smul (H := PhotonFock) volume (-Complex.I) _ _
      (PhysicalOneParticleEnergy.covariant_zero F χ C u (0, j))) hj

end PfHk.PhysicalOneParticleData

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
