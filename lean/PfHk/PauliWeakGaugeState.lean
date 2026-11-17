import PfHk.PauliWeakGauge
import PfHk.PauliGroundState
import GptLean.TransformationsGaugeWeakStates

/-! Weak spatial phases preserve normalized joint position--spin fermionic
states. The action is constructed on the actual common reference domain. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliWeakGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift GptLean.TransformationsGauge GptLean.TransformationsPhase
  PfHk.PauliGroundState

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

variable {N : ℕ}
local instance stateReferenceAddCommGroup : AddCommGroup (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceAddCommGroup (N := N)
local instance stateReferenceModule : Module ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceModule (N := N)
local instance stateReferenceSMul : SMul ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceSMul (N := N)
attribute [local irreducible] referenceSubspace inclusion

theorem reference_permutation (G : WeakSpatialGauge) (π : Equiv.Perm (Fin N))
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    PhysicalReferencePermutation.permutation π (G.gaugeReference (fun _ => 0) u) =
      G.gaugeReference (fun _ => 0) (PhysicalReferencePermutation.permutation π u) := by
  apply inclusion_injective (Fin N × Fin 3) (fun _ => 0)
  have hp : PhysicalReferencePermutation.pull π
      (G.wavePhase (inclusion (Fin N × Fin 3) (fun _ => 0) u)) =
      G.wavePhase (PhysicalReferencePermutation.pull π (inclusion (Fin N × Fin 3) (fun _ => 0) u)) :=
    G.permutation_wavePhase π (inclusion (Fin N × Fin 3) (fun _ => 0) u)
  exact (PhysicalReferencePermutation.inclusion_permutation π _).trans
    ((congrArg (PhysicalReferencePermutation.pull (Q := PhotonFock) π)
      (G.inclusion_gaugeReference (fun _ => 0) u)).trans
      (hp.trans ((congrArg G.wavePhase (PhysicalReferencePermutation.inclusion_permutation π u)).symm.trans
        (G.inclusion_gaugeReference (fun _ => 0) (PhysicalReferencePermutation.permutation π u)).symm)))

theorem gauge_smul (G : WeakSpatialGauge) (z : ℂ) (u : PauliGroundState.Ref N) :
    gauge G (z • u) = z • gauge G u := by
  funext s
  exact map_smul (G.gaugeReferenceLinear (fun _ => 0)) z (u s)

theorem joint_gauge (G : WeakSpatialGauge) (π : Equiv.Perm (Fin N))
    (u : PauliGroundState.Ref N) :
    jointPermutation π (gauge G u) = gauge G (jointPermutation π u) := by
  funext s
  exact reference_permutation G π (u (fun n => s (π.symm n)))

theorem fermionic_gauge (G : WeakSpatialGauge) (u : PauliGroundState.Ref N)
    (hu : Fermionic u) : Fermionic (gauge G u) := by
  intro π
  exact (joint_gauge G π u).trans
    ((congrArg (gauge G) (hu π)).trans (gauge_smul G _ u))

def gaugeState (G : WeakSpatialGauge) (p : State N) : State N where
  vector := gauge G p.vector
  normalized := (PauliReference.wave_norm_sq _).symm.trans
    ((congrArg (fun r : ℝ => r ^ 2) (wave_norm_gauge G p.vector)).trans
      ((PauliReference.wave_norm_sq p.vector).trans p.normalized))
  fermionic := fermionic_gauge G p.vector p.fermionic

theorem gaugeState_vector (G : WeakSpatialGauge) (p : State N) :
    (gaugeState G p).vector = gauge G p.vector := rfl

private theorem state_ext {p q : State N} (h : p.vector = q.vector) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem neg_gaugeState (G : WeakSpatialGauge) (p : State N) :
    gaugeState G.neg (gaugeState G p) = p :=
  state_ext (inverse_left G p.vector)

theorem gaugeState_neg (G : WeakSpatialGauge) (p : State N) :
    gaugeState G (gaugeState G.neg p) = p :=
  state_ext (inverse_right G p.vector)

theorem gaugeState_surjective (G : WeakSpatialGauge) :
    Function.Surjective (gaugeState (N := N) G) :=
  fun p => ⟨gaugeState G.neg p, gaugeState_neg G p⟩

end PfHk.PauliWeakGauge

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
