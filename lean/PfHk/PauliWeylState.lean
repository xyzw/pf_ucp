import PfHk.PauliWeyl
import PfHk.PauliGroundState

/-! Photon displacements preserve the normalized joint position and spin
fermionic state space of the actual Pauli form. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliWeyl

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalWeyl GptLean.Representability GptLean.SymmetricLift
  PfHk.PauliGroundState

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

variable {N : ℕ}

local instance stateReferenceAddCommGroup : AddCommGroup (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceAddCommGroup (N := N)
local instance stateReferenceModule : Module ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceModule (N := N)
local instance stateReferenceSMul : SMul ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceSMul (N := N)
attribute [local irreducible] referenceSubspace inclusion

variable (W : ConcreteWeylLaw photonMeasure) {f : Lp ℂ 2 photonMeasure}
  (K : WeightedPhotonKernel)
  (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)

theorem permutation_displaced (π : Equiv.Perm (Fin N)) (u : PauliGroundState.Ref N) :
    jointPermutation π (displaced W K hK u) =
      displaced W K hK (jointPermutation π u) := by
  funext s
  apply inclusion_injective (Fin N × Fin 3) (fun _ => 0)
  exact (PhysicalReferencePermutation.inclusion_permutation π _).trans
    ((congrArg (PhysicalReferencePermutation.pull π)
      (inclusion_weylRef (fun _ => 0) W K hK _)).trans
      ((PhysicalReferencePermutation.pull_compLpL π (weylOp W f) _).trans
        ((congrArg ((weylOp W f).compLpL 2 volume)
          (PhysicalReferencePermutation.inclusion_permutation π _).symm).trans
          (inclusion_weylRef (fun _ => 0) W K hK _).symm)))

theorem displaced_smul (a : ℂ) (u : PauliGroundState.Ref N) :
    displaced W K hK (a • u) = a • displaced W K hK u := by
  funext s
  exact (weylRef (fun _ => 0) W K hK).map_smul a (u s)

theorem fermionic_displaced (u : PauliGroundState.Ref N) (hu : Fermionic u) :
    Fermionic (displaced W K hK u) := by
  intro π
  exact (permutation_displaced W K hK π u).trans
    ((congrArg (displaced W K hK) (hu π)).trans
      (displaced_smul W K hK _ u))

def state (p : State N) : State N where
  vector := displaced W K hK p.vector
  normalized := by
    exact (PauliReference.wave_norm_sq _).symm.trans
      ((wave_norm_sq_displaced W K hK p.vector).trans
        ((PauliReference.wave_norm_sq _).trans p.normalized))
  fermionic := fermionic_displaced W K hK p.vector p.fermionic

end PfHk.PauliWeyl

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
