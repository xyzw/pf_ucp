import PfHk.PauliRawForm
import PfHk.PhysicalCommonFormDomain
import PfHk.PhysicalReferencePermutation
import PfHk.CenteredPhysicalReference

/-! The actual Pauli form on finite families of photon-valued reference
vectors. External multipliers are constructed from the global potential
classes. Pure states are normalized and antisymmetric under simultaneous
position and spin permutations. Ground states minimize this Pauli form.
No spinful variational or continuation conclusion is postulated. -/

noncomputable section
namespace PfHk.PauliGroundState

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPairSpace GptLean.PhysicalPolarization
  GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PauliCurrentAlgebra PfHk.PhysicalLocalEnergy
  PfHk.PhysicalCommonFormDomain PfHk.CenteredPhysicalReference
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

variable {N : ℕ}

local instance referenceAddCommGroup : AddCommGroup (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  (referenceSubspace (Fin N × Fin 3) (fun _ => 0)).addCommGroup
local instance referenceModule : Module ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  (referenceSubspace (Fin N × Fin 3) (fun _ => 0)).module
local instance referenceSMul : SMul ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  (referenceModule (N := N)).toSMul

attribute [local irreducible] referenceSubspace

variable (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

section Physical
variable (F : Frame) (χ : ArticleCutoff)

theorem physicalDomain (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (u : Ref N) : Domain (vector A) (positive v c) (negative v c) u :=
  fun s => externalDomain A v c hc (u s)

def form (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (z u : Ref N) : ℂ :=
  rawForm C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
    (profile_bound F χ 0) e (vector A) (positive v c) (negative v c) z u
    (physicalDomain A v c hc z) (physicalDomain A v c hc u)

def energy (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (u : Ref N) : ℝ := (form C e F χ A v c hc u u).re


end Physical

/-- Pull back position and spin by the same electron permutation. -/
def jointPermutation (π : Equiv.Perm (Fin N)) (u : Ref N) : Ref N :=
  fun s => PhysicalReferencePermutation.permutation π (u (fun n => s (π.symm n)))

def Fermionic (u : Ref N) : Prop :=
  ∀ π : Equiv.Perm (Fin N),
    jointPermutation π u =
      @SMul.smul ℂ (Ref N) inferInstance
        (PhysicalElectronicFermions.signCharacter N π) u

structure State (N : ℕ) where
  vector : Ref N
  normalized : normSquared vector = 1
  fermionic : Fermionic vector

theorem State.wave_norm (p : State N) : ‖PauliReference.wave p.vector‖ = 1 := by
  have h : ‖PauliReference.wave p.vector‖ ^ 2 = 1 :=
    (PauliReference.wave_norm_sq p.vector).trans p.normalized
  nlinarith [norm_nonneg (PauliReference.wave p.vector)]

theorem State.vector_ne_zero (p : State N) : p.vector ≠ 0 := by
  intro hz
  have hw : PauliReference.wave p.vector = 0 :=
    (congrArg (PauliReference.wave (N := N)) hz).trans PauliReference.wave_zero
  have h : (0 : ℝ) = 1 := by
    simpa only [norm_zero] using (congrArg norm hw).symm.trans p.wave_norm
  exact zero_ne_one h

def IsGroundState (F : Frame) (χ : ArticleCutoff) (A : VectorPotential)
    (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c) (p : State N) : Prop :=
  ∀ q : State N, energy C e F χ A v c hc p.vector ≤ energy C e F χ A v c hc q.vector

end PfHk.PauliGroundState
