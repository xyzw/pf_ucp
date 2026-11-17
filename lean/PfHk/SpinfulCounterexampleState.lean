import PfHk.CounterexampleVacuumState
import PfHk.PauliCurrentGroundState
import PfHk.SpinfulCounterexampleSpin

/-! The normalized spin-down hydrogen orbital in the photon vacuum, as an
actual state of the Pauli form on the common reference domain. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.SpinfulCounterexampleState

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PauliSpin PfHk.PauliGroundState
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

local instance referenceAddCommGroup : AddCommGroup (Reference (Fin 1 × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceAddCommGroup (N := 1)
local instance referenceModule : Module ℂ (Reference (Fin 1 × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceModule (N := 1)
local instance referenceSMul : SMul ℂ (Reference (Fin 1 × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceSMul (N := 1)

attribute [local irreducible] inclusion ordinary radiation referenceSubspace

abbrev Index := Fin 1 × Fin 3
abbrev OrbitalRef := PhysicalOneParticleState.Ref

/-- Embed an orbital reference vector in the down-spin component. -/
def liftDown (u : OrbitalRef) : PauliReference.Ref 1 :=
  fun s => if s 0 = 1 then u else 0

@[simp] theorem liftDown_up (u : OrbitalRef) : liftDown u up = 0 := by
  simp [liftDown, up]

@[simp] theorem liftDown_down (u : OrbitalRef) : liftDown u down = u := by
  simp [liftDown, down]

theorem liftDown_smul (c : ℂ) (u : OrbitalRef) :
    liftDown (c • u) = c • liftDown u := by
  funext s
  by_cases hs : s 0 = 1 <;> simp [liftDown, hs]

theorem eq_liftDown_of_up_zero (u : PauliReference.Ref 1) (hu : u up = 0) :
    u = liftDown (u down) := by
  funext s
  rcases spin_cases s with rfl | rfl
  · exact hu.trans (liftDown_up _).symm
  · exact (liftDown_down _).symm

theorem normSquared_liftDown (u : OrbitalRef) :
    normSquared (liftDown u) = ‖inclusion Index (fun _ => 0) u‖ ^ 2 := by
  have hzero : ‖inclusion Index (fun _ => 0) (liftDown u up)‖ ^ 2 = 0 :=
    (congrArg (fun v : OrbitalRef => ‖inclusion Index (fun _ => 0) v‖ ^ 2)
      (liftDown_up u)).trans
        ((congrArg (fun w : WaveSpace Index => ‖w‖ ^ 2)
          (inclusion Index (fun _ => 0)).map_zero).trans (by simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]))
  have hdown : ‖inclusion Index (fun _ => 0) (liftDown u down)‖ ^ 2 =
      ‖inclusion Index (fun _ => 0) u‖ ^ 2 :=
    congrArg (fun v : OrbitalRef => ‖inclusion Index (fun _ => 0) v‖ ^ 2) (liftDown_down u)
  exact (sum_spin (fun s => ‖inclusion Index (fun _ => 0) (liftDown u s)‖ ^ 2)).trans
    ((congrArg₂ (fun a b : ℝ => a + b) hzero hdown).trans (zero_add _))

/-- One-electron antisymmetry imposes no additional condition on spinors. -/
theorem fermionic_one (u : PauliReference.Ref 1) : Fermionic u := by
  intro π
  have hπ : π = 1 := Subsingleton.elim _ _
  subst π
  have hp : jointPermutation (1 : Equiv.Perm (Fin 1)) u = u := by
    funext s
    exact PhysicalReferencePermutation.permutation_one (u s)
  have hs : PhysicalElectronicFermions.signCharacter 1 (1 : Equiv.Perm (Fin 1)) = (1 : ℂ) := by
    simp [PhysicalElectronicFermions.signCharacter]
  change jointPermutation (1 : Equiv.Perm (Fin 1)) u =
    PhysicalElectronicFermions.signCharacter 1 (1 : Equiv.Perm (Fin 1)) • u
  exact hp.trans ((congrArg (fun c : ℂ => c • u) hs).trans (one_smul ℂ u)).symm

def reference (Z : ℝ) (hZ : 0 < Z) : PauliReference.Ref 1 :=
  liftDown (CounterexampleVacuumState.reference Z hZ)

@[simp] theorem reference_up (Z : ℝ) (hZ : 0 < Z) : reference Z hZ up = 0 :=
  liftDown_up _

@[simp] theorem reference_down (Z : ℝ) (hZ : 0 < Z) :
    reference Z hZ down = CounterexampleVacuumState.reference Z hZ :=
  liftDown_down _

theorem reference_normalized (Z : ℝ) (hZ : 0 < Z) :
    normSquared (reference Z hZ) = 1 := by
  rw [reference, normSquared_liftDown, CounterexampleVacuumState.reference_norm]
  norm_num

def state (Z : ℝ) (hZ : 0 < Z) : PauliGroundState.State 1 where
  vector := reference Z hZ
  normalized := reference_normalized Z hZ
  fermionic := fermionic_one _

@[simp] theorem state_vector (Z : ℝ) (hZ : 0 < Z) :
    (state Z hZ).vector = reference Z hZ := rfl

/-- The fixed unit spin--photon fiber carrying spin down and the vacuum. -/
def vacuumDown : Fiber 1 PhotonFock :=
  WithLp.toLp 2 (fun s => if s 0 = 1 then PhysicalFullVacuum.vacuum else 0)

theorem vacuumDown_norm : ‖vacuumDown‖ = 1 := by
  have hsq : ‖vacuumDown‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2, sum_spin]
    simp [vacuumDown, up, down, PhysicalFullVacuum.vacuum_norm]
  nlinarith [norm_nonneg vacuumDown]

theorem reference_wave_ae (Z : ℝ) (hZ : 0 < Z) :
    PauliReference.wave (reference Z hZ) =ᵐ[volume]
      fun X => (HydrogenOrbital.orbital Z (SymmetricLift.particle X 0) : ℂ) • vacuumDown := by
  filter_upwards [PauliReference.wave_ae (reference Z hZ),
    CounterexampleVacuumState.reference_value_ae Z hZ,
    Lp.coeFn_zero PhotonFock 2 (volume : Measure (Position Index))] with X hw hv hzero
  rw [hw]
  apply PiLp.ext
  intro s
  by_cases hs : s 0 = 1
  · simpa only [reference, liftDown, hs, ite_true, vacuumDown,
      PiLp.smul_apply, PiLp.toLp_apply] using hv
  · simp only [reference, liftDown, hs, ite_false, map_zero, hzero, Pi.zero_apply,
      vacuumDown, PiLp.smul_apply, smul_zero]

end PfHk.SpinfulCounterexampleState
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
