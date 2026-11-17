import PfHk.CounterexamplePhysicalEnergy
import PfHk.CounterexampleVacuumState
import PfHk.PhysicalReferenceVacuum
import PfHk.PhysicalOneParticleData

/-! The common unique ground state of the physical zero-coupling magnetic
family. All states and energies belong to the original Pauli--Fierz model. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PhysicalZeroCouplingCounterexample

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms GptLean.PhysicalPairSpace
  PfHk.PhysicalOneParticleState PfHk.CounterexampleVacuumState

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 250000

local instance photonRealInner : InnerProductSpace ℝ PhotonFock :=
  CounterexampleSpectral.photonRealInner

attribute [local irreducible] inclusion radiation PhysicalPFReference.referenceSubspace
  PhysicalGroundStateWeak.stateReference

private theorem norm_sq_scalar_ae {Q H : Type*} [MeasurableSpace Q]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {μ : Measure Q}
    (v : H) (hv : ‖v‖ = 1) {f : Q → H} {a : Q → ℝ}
    (hf : f =ᵐ[μ] fun X => (a X : ℂ) • v) :
    (fun X => ‖f X‖ ^ 2) =ᵐ[μ] fun X => a X ^ 2 := by
  filter_upwards [hf] with X hX
  rw [hX, norm_smul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

variable (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground)

def potentials (Z t : ℝ) : PhysicalPairDuality.Potential :=
  PhysicalDiamagneticPotential.shifted (CounterexamplePotentials.scalar Z t)
    (CounterexamplePotentials.vector t)

/-- Every member has the same energy on the explicitly constructed state. -/
theorem state_energy (Z : ℝ) (hZ : 0 < Z) (t : ℝ) :
    shiftedEnergy (0 : Fin 1) F χ C B S 0 (potentials Z t)
      (state F χ C B S Z hZ) = -(Z ^ 2 / 2) := by
  have he := CounterexamplePhysicalEnergy.shiftedEnergy F χ C B S Z t
    (state F χ C B S Z hZ) (reference Z hZ) rfl
  have hr : ‖radiation Index (fun _ => 0) (reference Z hZ)‖ ^ 2 = 0 :=
    (congrArg (fun v : WaveSpace Index => ‖v‖ ^ 2) (reference_radiation Z hZ)).trans
      (by simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)])
  exact he.trans ((congrArg₂ (fun x y : ℝ => x + y)
    (reference_electronic_energy Z hZ t) hr).trans (add_zero _))

variable (D : CounterexampleSpectral.StandardSphericalDecomposition)

include D in
/-- The lower bound is proved for every normalized physical state. -/
theorem energy_lower_bound (Z : ℝ) {t : ℝ} (ht : |t| ≤ 1)
    (p : State F χ C B S 0 (N := 1)) :
    -(Z ^ 2 / 2) ≤ shiftedEnergy (0 : Fin 1) F χ C B S 0 (potentials Z t) p := by
  let u := PhysicalGroundStateWeak.stateReference F χ C B S 0 p
  have hu := PhysicalGroundStateWeak.stateReference_value F χ C B S 0 p
  have he := CounterexamplePhysicalEnergy.shiftedEnergy F χ C B S Z t p u hu
  have hn : ‖ElectronicH1Complex.value (E := PhotonFock) (I := Index) (electronic Index (fun _ => 0) u)‖ = 1 :=
    (congrArg norm ((CounterexamplePhysicalEnergy.value_electronic u).trans hu)).trans
      p.property.1
  have hl := CounterexampleSpectral.energy_lower_bound D Z ht (electronic Index (fun _ => 0) u)
  have hl' := (CounterexampleEnergyAlgebra.normalized_level Z _ hn).symm.le.trans hl
  exact CounterexampleEnergyAlgebra.lower_bound hl'
    (sq_nonneg ‖radiation Index (fun _ => 0) u‖) he

include D in
/-- The hydrogen orbital times the photon vacuum is a ground state of
every physical Hamiltonian in the family for |t|<1. -/
theorem ground_state (Z : ℝ) (hZ : 0 < Z) {t : ℝ} (ht : |t| < 1) :
    IsGroundState (0 : Fin 1) F χ C B S 0 (potentials Z t)
      (state F χ C B S Z hZ) := by
  intro p
  exact (state_energy F χ C B S Z hZ t).le.trans
    (energy_lower_bound F χ C B S D Z ht.le p)

variable (O : CounterexampleSpectral.StandardRadialWeakODE (E := PhotonFock))
  (BF : StandardSymmetricFockExponential)

include D O BF in
/-- Every normalized ground state is a single unimodular multiple of the
same explicit state. No positive spectral gap is assumed. -/
theorem unique_ground_state (Z : ℝ) (hZ : 0 < Z) {t : ℝ} (ht : |t| < 1)
    (p : State F χ C B S 0 (N := 1))
    (hp : IsGroundState (0 : Fin 1) F χ C B S 0 (potentials Z t) p) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ p.val = c • (state F χ C B S Z hZ).val := by
  let u := PhysicalGroundStateWeak.stateReference F χ C B S 0 p
  have hu := PhysicalGroundStateWeak.stateReference_value F χ C B S 0 p
  have hn : ‖inclusion Index (fun _ => 0) u‖ = 1 := (congrArg norm hu).trans p.property.1
  have hupper := hp (state F χ C B S Z hZ)
  have hupper' := hupper.trans_eq (state_energy F χ C B S Z hZ t)
  have he := CounterexamplePhysicalEnergy.shiftedEnergy F χ C B S Z t p u hu
  have hl := CounterexampleSpectral.energy_lower_bound D Z ht.le
    (electronic Index (fun _ => 0) u)
  have hnorm : ‖ElectronicH1Complex.value (E := PhotonFock) (I := Index) (electronic Index (fun _ => 0) u)‖ = 1 :=
    (congrArg norm (CounterexamplePhysicalEnergy.value_electronic u)).trans hn
  have hl' := (CounterexampleEnergyAlgebra.normalized_level Z _ hnorm).symm.le.trans hl
  have hparts := CounterexampleEnergyAlgebra.equality_parts hl'
    (sq_nonneg ‖radiation Index (fun _ => 0) u‖) he hupper'
  have hr : radiation Index (fun _ => 0) u = 0 := by
    apply norm_eq_zero.mp
    exact CounterexampleEnergyAlgebra.zero_of_square_zero hparts.2
  have hex := CounterexampleSpectral.energy_equality_radial D O hZ ht
    (electronic Index (fun _ => 0) u)
    (hparts.1.trans (CounterexampleEnergyAlgebra.normalized_level Z _ hnorm).symm)
  rcases hex with ⟨v, hv⟩
  have hv' : inclusion Index (fun _ => 0) u =ᵐ[volume] fun X =>
      (HydrogenOrbital.orbital Z (SymmetricLift.particle X 0) : ℂ) • v := by
    filter_upwards [hv] with X hX
    have hx := congrArg (fun w : WaveSpace Index => w X)
      (CounterexamplePhysicalEnergy.value_electronic u).symm
    exact hx.trans (hX.trans (RCLike.real_smul_eq_coe_smul (K := ℂ)
      (HydrogenOrbital.orbital Z (SymmetricLift.particle X 0)) v))

  have hphase := PhysicalReferenceVacuum.phase_of_electronic_factor BF u
    (inclusion Index (fun _ => 0) (reference Z hZ))
    (fun X => HydrogenOrbital.orbital Z (SymmetricLift.particle X 0))
    (fun X => (HydrogenOrbital.orbital_pos hZ _).ne')
    (reference_value_ae Z hZ) hn (reference_norm Z hZ) hr v hv'
  rcases hphase with ⟨c, hc, hval⟩
  exact ⟨c, hc, hu.symm.trans hval⟩

/-- The actual density has the explicit hydrogenic formula. -/
theorem state_density (Z : ℝ) (hZ : 0 < Z) :
    densityL1 ((model (0 : Fin 1) F χ C B S 0).density (state F χ C B S Z hZ)) =ᵐ[volume]
      HydrogenOrbital.density Z := by
  have hd := PhysicalOneParticleData.density F χ C B S 0 (state F χ C B S Z hZ)
  have hn := norm_sq_scalar_ae PhysicalFullVacuum.vacuum PhysicalFullVacuum.vacuum_norm
    (reference_value_ae Z hZ)
  have hv := PhysicalOneParticleData.ae_configuration hn
  filter_upwards [hd, hv] with x hx hvx
  have hs := congrArg (fun ψ : WaveSpace Index =>
    ‖ψ (PhysicalOneParticleData.configuration x)‖ ^ 2) (state_value F χ C B S Z hZ)
  exact hx.trans (hs.trans (hvx.trans (by
    simpa only [PhysicalOneParticleData.configuration_particle] using
      HydrogenOrbital.orbital_sq hZ.le x)))

/-- The actual combined current vanishes at zero coupling. -/
theorem state_current (Z : ℝ) (hZ : 0 < Z) :
    currentL1 ((model (0 : Fin 1) F χ C B S 0).density (state F χ C B S Z hZ)) =ᵐ[volume] 0 :=
  PhysicalOneParticleData.current_zero F χ C B S (state F χ C B S Z hZ)
    (reference Z hZ) rfl (reference_current Z hZ)

/-- Every exponent below twice the nuclear charge is an actual density
moment of the constructed model state. -/
theorem state_exponential_moment (Z : ℝ) (hZ : 0 < Z) {α : ℝ} (hα : α < 2 * Z) :
    Integrable (fun x => Real.exp (α * ‖x‖) * densityL1
      ((model (0 : Fin 1) F χ C B S 0).density (state F χ C B S Z hZ)) x) volume := by
  apply (HydrogenOrbital.exponential_moment hZ hα).congr
  filter_upwards [state_density F χ C B S Z hZ] with x hx
  rw [hx]

end PfHk.PhysicalZeroCouplingCounterexample

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
