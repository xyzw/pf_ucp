import PfHk.SpinfulCounterexampleState
import PfHk.PhysicalOneParticleData
import PfHk.PauliCurrentMagnetization

/-! Actual spin-summed density, magnetization and Pauli current of the
spin-down hydrogen-vacuum state. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.SpinfulCounterexampleData

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.PhysicalPairSpace GptLean.PhysicalSourceCoordinates
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.SpinfulCounterexampleState
  PfHk.PauliCurrentCorrection PfHk.PauliMagnetizationMarginal
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

local instance remaining_empty : IsEmpty (Remaining (0 : Fin 1)) :=
  ⟨fun j => j.1.property (Subsingleton.elim _ _)⟩

local instance referenceAddCommGroup : AddCommGroup (Reference (Fin 1 × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceAddCommGroup (N := 1)
local instance referenceModule : Module ℂ (Reference (Fin 1 × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceModule (N := 1)
local instance referenceSMul : SMul ℂ (Reference (Fin 1 × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceSMul (N := 1)

attribute [local irreducible] inclusion ordinary covariant radiation
  PhysicalPFReference.referenceSubspace ElectronicH1Complex.complexWeakGraph
  ElectronicH1Complex.value ElectronicH1Complex.derivative

/-- The combined current `-(1/2) curl (rho e_3)` of the spin-down orbital. -/
def current (Z : ℝ) (x : Gaussian.FieldSpace) : Vector :=
  (Z * HydrogenOrbital.density Z x / ‖x‖) • WithLp.toLp 2 ![x 1, -x 0, 0]

theorem reference_values_ae (Z : ℝ) (hZ : 0 < Z) :
    ∀ᵐ X ∂volume, (fun s => inclusion Index (fun _ => 0) (reference Z hZ s) X) =
      downFamily ((HydrogenOrbital.orbital Z (SymmetricLift.particle X 0) : ℂ) •
        PhysicalFullVacuum.vacuum) := by
  filter_upwards [CounterexampleVacuumState.reference_value_ae Z hZ,
    Lp.coeFn_zero PhotonFock 2 (volume : Measure (PhysicalPFReference.Position Index))]
    with X hv hz
  funext s
  by_cases hs : s 0 = 1
  · simpa only [reference, liftDown, downFamily, hs, ite_true] using hv
  · simp only [reference, liftDown, downFamily, hs, ite_false, map_zero, hz, Pi.zero_apply]

theorem reference_derivatives_ae (Z : ℝ) (hZ : 0 < Z) (j : Fin 3) :
    ∀ᵐ X ∂volume,
      (fun s => ordinary Index (fun _ => 0) (0,j) (reference Z hZ s) X) =
      downFamily ((HydrogenOrbital.derivative Z j (SymmetricLift.particle X 0) : ℂ) •
        PhysicalFullVacuum.vacuum) := by
  filter_upwards [CounterexampleVacuumState.reference_ordinary_ae Z hZ (0,j),
    Lp.coeFn_zero PhotonFock 2 (volume : Measure (PhysicalPFReference.Position Index))]
    with X hv hz
  funext s
  by_cases hs : s 0 = 1
  · simpa only [reference, liftDown, downFamily, hs, ite_true] using hv
  · simp only [reference, liftDown, downFamily, hs, ite_false, map_zero, hz, Pi.zero_apply]

/-- For one electron the spectator space is a point, so every marginal is
evaluation at the embedded configuration. -/
private theorem one_marginal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : _ → E) (x : Gaussian.FieldSpace) :
    (∫ y, f ((split (0 : Fin 1)).symm (x, y))) = f (PhysicalOneParticleData.configuration x) := by
  rw [volume_euclideanSpace_eq_dirac, integral_dirac]
  rfl

private theorem real_inner (a b : ℝ) :
    (inner ℂ ((a : ℂ) • PhysicalFullVacuum.vacuum)
      ((b : ℂ) • PhysicalFullVacuum.vacuum)).re = a * b := by
  rw [inner_smul_right, inner_smul_left]
  simp [inner_self_eq_norm_sq_to_K, PhysicalFullVacuum.vacuum_norm, Complex.mul_re, mul_comm]

private theorem real_momentum_inner (a b : ℝ) :
    inner ℂ ((a : ℂ) • PhysicalFullVacuum.vacuum)
      ((-Complex.I) • ((b : ℂ) • PhysicalFullVacuum.vacuum)) =
      -Complex.I * (a * b : ℝ) := by
  rw [inner_smul_right, inner_smul_right, inner_smul_left]
  simp [inner_self_eq_norm_sq_to_K, PhysicalFullVacuum.vacuum_norm]
  ring

/-- The pointwise Pauli current of a spin-down spinor. Only the spin
(magnetization-curl) part survives when the orbital part vanishes. -/
private theorem current_down_point {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (w : H) (v : Fin 3 → H) (hre : ∀ k, (inner ℂ w (v k)).re = 0) (j : Fin 3) :
    PauliCurrentAlgebra.current (0 : Fin 1) (downFamily w) (fun k => downFamily (v k)) j =
      ![(inner ℂ w (v 1)).im, -(inner ℂ w (v 0)).im, 0] j := by
  have hpair (k l : Fin 3) :
      (spinPair (0 : Fin 1) (downFamily w) (downFamily (v k)) l).im =
        if l = 2 then -(inner ℂ w (v k)).im else 0 := by
    rw [spinPair_down]
    split_ifs <;> simp
  have horb (k : Fin 3) : orbitalCurrent (downFamily w) (fun k => downFamily (v k)) k = 0 := by
    simp only [orbitalCurrent, sum_spin, downFamily_up, downFamily_down, inner_zero_left, zero_add]
    exact hre k
  have h0 := current_zero (0 : Fin 1) (downFamily w) (fun k => downFamily (v k))
  have h1 := current_one (0 : Fin 1) (downFamily w) (fun k => downFamily (v k))
  have h2 := current_two (0 : Fin 1) (downFamily w) (fun k => downFamily (v k))
  rw [horb, hpair, hpair] at h0 h1 h2
  fin_cases j
  · simpa using h0
  · simpa using h1
  · simpa using h2

private theorem current_down (a : ℝ) (b : Fin 3 → ℝ) (j : Fin 3) :
    PauliCurrentAlgebra.current (0 : Fin 1)
      (downFamily ((a : ℂ) • PhysicalFullVacuum.vacuum))
      (fun k => downFamily ((-Complex.I) • ((b k : ℂ) • PhysicalFullVacuum.vacuum))) j =
      ![-a * b 1, a * b 0, 0] j := by
  have hre (k : Fin 3) : (inner ℂ ((a : ℂ) • PhysicalFullVacuum.vacuum)
      ((-Complex.I) • ((b k : ℂ) • PhysicalFullVacuum.vacuum))).re = 0 := by
    rw [real_momentum_inner]
    simp
  rw [current_down_point ((a : ℂ) • PhysicalFullVacuum.vacuum)
    (fun k => (-Complex.I) • ((b k : ℂ) • PhysicalFullVacuum.vacuum)) hre j,
    real_momentum_inner, real_momentum_inner]
  fin_cases j <;> simp

private theorem hydrogen_current (Z : ℝ) (hZ : 0 < Z)
    (x : Gaussian.FieldSpace) (j : Fin 3) :
    ![-HydrogenOrbital.orbital Z x * HydrogenOrbital.derivative Z 1 x,
      HydrogenOrbital.orbital Z x * HydrogenOrbital.derivative Z 0 x, 0] j =
      current Z x j := by
  have hρ := HydrogenOrbital.orbital_sq hZ.le x
  fin_cases j <;>
    simp [current, HydrogenOrbital.derivative, ← hρ] <;> ring

variable (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff)

private theorem covariants_zero (u : PauliReference.Ref 1) (j : Fin 3) (s : SpinIndex 1) :
    covariants C 0 F χ u (0,j) s =
      (-Complex.I) • ordinary Index (fun _ => 0) (0,j) (u s) := by
  exact (covariant_apply Index (fun _ => 0) C (CenteredPhysicalReference.profile F χ 0)
    (CenteredPhysicalReference.profile_measurable F χ 0)
    (CenteredPhysicalReference.profileBound F χ) (CenteredPhysicalReference.profile_bound F χ 0)
    0 (0,j) (u s)).trans (by simp only [Complex.ofReal_zero, zero_smul, sub_zero])

private theorem reference_covariants_ae (Z : ℝ) (hZ : 0 < Z) (j : Fin 3) :
    ∀ᵐ X ∂volume,
      (fun s => covariants C 0 F χ (reference Z hZ) (0,j) s X) =
      downFamily ((-Complex.I) •
        ((HydrogenOrbital.derivative Z j (SymmetricLift.particle X 0) : ℂ) •
          PhysicalFullVacuum.vacuum)) := by
  have hsmul (s : SpinIndex 1) := Lp.coeFn_smul (-Complex.I)
    (ordinary Index (fun _ => 0) (0,j) (reference Z hZ s))
  filter_upwards [ae_all_iff.mpr hsmul, reference_derivatives_ae Z hZ j] with X hX hd
  funext s
  have hds : ordinary Index (fun _ => 0) (0,j) (reference Z hZ s) X =
      downFamily ((HydrogenOrbital.derivative Z j (SymmetricLift.particle X 0) : ℂ) •
        PhysicalFullVacuum.vacuum) s := congrFun hd s
  have hcov : covariants C 0 F χ (reference Z hZ) (0,j) s X =
      (-Complex.I) • ordinary Index (fun _ => 0) (0,j) (reference Z hZ s) X :=
    (congrArg (fun w : ElectronicH1Space.L2 PhotonFock Index => w X)
      (covariants_zero C F χ (reference Z hZ) j s)).trans (hX s)
  rw [hcov, hds]
  rcases spin_cases s with rfl | rfl <;> simp

private theorem data_eq (Z : ℝ) (hZ : 0 < Z) :
    data C 0 F χ (reference Z hZ) = PauliCurrent.particlePair (0 : Fin 1)
      (PauliCurrentMagnetization.components (reference Z hZ))
      (covariants C 0 F χ (reference Z hZ)) := by
  unfold data
  change PauliCurrent.pair (PauliCurrentMagnetization.components (reference Z hZ))
    (covariants C 0 F χ (reference Z hZ)) = _
  rw [PauliCurrent.pair_def]
  simp only [Nat.cast_one, inv_one, one_smul, Fin.sum_univ_one]

private theorem wave_eq (Z : ℝ) (hZ : 0 < Z) :
    PauliCurrent.wave (PauliCurrentMagnetization.components (reference Z hZ)) =
      PauliReference.wave (reference Z hZ) := by
  unfold PauliCurrent.wave PauliCurrentMagnetization.components PauliReference.wave inclusion
  rfl

theorem density (Z : ℝ) (hZ : 0 < Z) :
    densityL1 (data C 0 F χ (reference Z hZ)) =ᵐ[volume] HydrogenOrbital.density Z := by
  let u := PauliCurrentMagnetization.components (reference Z hZ)
  let d := covariants C 0 F χ (reference Z hZ)
  rw [data_eq C F χ Z hZ]
  filter_upwards [PauliCurrent.particle_density_ae (0 : Fin 1) u d,
    PhysicalOneParticleData.ae_configuration (reference_wave_ae Z hZ)] with x hρ hv
  have hw : PauliCurrent.wave u (PhysicalOneParticleData.configuration x) =
      (HydrogenOrbital.orbital Z (SymmetricLift.particle
        (PhysicalOneParticleData.configuration x) 0) : ℂ) • vacuumDown :=
    (congrArg (fun w : PauliCurrent.Wave (N := 1) => w (PhysicalOneParticleData.configuration x))
      (wave_eq Z hZ)).trans hv
  have hm : (∫ y, ‖PauliCurrent.wave u ((split (0 : Fin 1)).symm (x, y))‖ ^ 2) =
      ‖PauliCurrent.wave u (PhysicalOneParticleData.configuration x)‖ ^ 2 :=
    one_marginal (fun X => ‖PauliCurrent.wave u X‖ ^ 2) x
  have hn : ‖PauliCurrent.wave u (PhysicalOneParticleData.configuration x)‖ ^ 2 =
      HydrogenOrbital.density Z x := by
    rw [hw, norm_smul, vacuumDown_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      PhysicalOneParticleData.configuration_particle]
    exact HydrogenOrbital.orbital_sq hZ.le x
  refine hρ.trans ?_
  rw [hm, hn]
  simp only [Nat.cast_one, one_mul]

/-- The generic magnetization density on the actual reference components.
The generic instances are compared with the concrete ones only once, by
definitional unfolding, as in `PauliCurrentMagnetization`. -/
private theorem magnetization_configuration (u : PauliReference.Ref 1) (k : Fin 3)
    (X : PhysicalPFReference.Position Index) :
    PauliMagnetizationDistribution.magnetization (0 : Fin 1)
      (PauliCurrentMagnetization.components u) k X =
      (spinPair (0 : Fin 1) (fun s => inclusion Index (fun _ => 0) (u s) X)
        (fun s => inclusion Index (fun _ => 0) (u s) X) k).re := by
  unfold PauliMagnetizationDistribution.magnetization PauliMagnetizationLp.pointPair
    PauliCurrentMagnetization.components inclusion
  rfl

private theorem down_magnetization (a : ℝ) (k : Fin 3) :
    (spinPair (0 : Fin 1) (downFamily ((a : ℂ) • PhysicalFullVacuum.vacuum))
      (downFamily ((a : ℂ) • PhysicalFullVacuum.vacuum)) k).re =
      if k = 2 then -(a ^ 2) else 0 := by
  rw [spinPair_down]
  split_ifs
  · rw [Complex.neg_re, real_inner, pow_two]
  · rfl

theorem magnetization (Z : ℝ) (hZ : 0 < Z) (k : Fin 3) :
    PauliMagnetizationMarginal.magnetization
      (PauliCurrentMagnetization.components (reference Z hZ)) k =ᵐ[volume]
      fun x => if k = 2 then -HydrogenOrbital.density Z x else 0 := by
  have hm : PauliMagnetizationDistribution.magnetization (0 : Fin 1)
      (PauliCurrentMagnetization.components (reference Z hZ)) k =ᵐ[volume]
        fun X => if k = 2 then -HydrogenOrbital.density Z (SymmetricLift.particle X 0) else 0 := by
    filter_upwards [reference_values_ae Z hZ] with X hv
    rw [magnetization_configuration (reference Z hZ) k X, hv, down_magnetization,
      HydrogenOrbital.orbital_sq hZ.le]
  filter_upwards [PhysicalOneParticleData.ae_configuration hm] with x hx
  have hmarg := one_marginal (PauliMagnetizationDistribution.magnetization (0 : Fin 1)
    (PauliCurrentMagnetization.components (reference Z hZ)) k) x
  unfold PauliMagnetizationMarginal.magnetization marginal
  rw [Fin.sum_univ_one, hmarg, hx, PhysicalOneParticleData.configuration_particle]

theorem combined_current (Z : ℝ) (hZ : 0 < Z) :
    currentL1 (data C 0 F χ (reference Z hZ)) =ᵐ[volume] current Z := by
  let u := PauliCurrentMagnetization.components (reference Z hZ)
  let d := covariants C 0 F χ (reference Z hZ)
  have hc (j : Fin 3) :
      (fun X => (inner ℂ (PauliCurrent.wave u X)
        (PauliCurrent.pauliVelocity d (0 : Fin 1) j X)).re) =ᵐ[volume]
        fun X => current Z (SymmetricLift.particle X 0) j := by
    filter_upwards [PauliExternalEnergy.current_ae (0 : Fin 1) u d j,
      reference_values_ae Z hZ,
      ae_all_iff.mpr (reference_covariants_ae C F χ Z hZ)] with X hj hv hd
    have hval : (fun s => ElectronicH1Complex.value (u s) X) =
        downFamily ((HydrogenOrbital.orbital Z (SymmetricLift.particle X 0) : ℂ) •
          PhysicalFullVacuum.vacuum) :=
      (funext fun s => congrArg (fun w : ElectronicH1Space.L2 PhotonFock Index => w X)
        (PauliCurrentMagnetization.components_value (reference Z hZ) s)).trans hv
    have hder : (fun b s => d (0,b) s X) =
        (fun b => downFamily ((-Complex.I) •
          ((HydrogenOrbital.derivative Z b (SymmetricLift.particle X 0) : ℂ) •
            PhysicalFullVacuum.vacuum))) := funext hd
    exact hj.trans ((congrArg₂ (fun (v : SpinIndex 1 → PhotonFock)
        (w : Fin 3 → SpinIndex 1 → PhotonFock) => PauliCurrentAlgebra.current (0 : Fin 1) v w j)
      hval hder).trans ((current_down _ _ j).trans (hydrogen_current Z hZ _ j)))
  have hj (j : Fin 3) : (fun x => currentL1 (data C 0 F χ (reference Z hZ)) x j) =ᵐ[volume]
      fun x => current Z x j := by
    filter_upwards [PauliPairCovariance.pair_current_ae (by decide : 0 < 1) u d j,
      PhysicalOneParticleData.ae_configuration (hc j)] with x hp hcj
    have hmarg := one_marginal (fun X => inner ℂ (PauliCurrent.wave u X)
      (PauliCurrent.pauliVelocity d (0 : Fin 1) j X)) x
    change currentL1 (PauliCurrent.pair u d) x j = _
    rw [hp, Fin.sum_univ_one, hmarg]
    rw [PhysicalOneParticleData.configuration_particle] at hcj
    exact hcj
  filter_upwards [ae_all_iff.mpr hj] with x hx
  apply PiLp.ext
  intro j
  exact hx j

theorem exponential_moment (Z : ℝ) (hZ : 0 < Z) {α : ℝ} (hα : α < 2 * Z) :
    Integrable (fun x => Real.exp (α * ‖x‖) *
      densityL1 (data C 0 F χ (reference Z hZ)) x) volume := by
  refine (HydrogenOrbital.exponential_moment hZ hα).congr ?_
  filter_upwards [density C F χ Z hZ] with x hx
  rw [hx]

end PfHk.SpinfulCounterexampleData
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
