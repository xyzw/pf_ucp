import PfHk.PauliGroundStateWeak
import PfHk.PauliPermutation
import PfHk.PhysicalFermionicAverage
import PfHk.SignTwistedReduction

/-! The concrete joint-spin Pauli form has an unrestricted weak equation.
Its tests are extended from the fermionic sector by the proved finite
permutation symmetry, with no extension principle assumed. -/

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

noncomputable section
namespace PfHk.PauliGroundStateWeak

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.CenteredPhysicalReference
  PfHk.PhysicalCommonFormDomain PfHk.PhysicalLocalEnergy

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

variable {N : ℕ}
attribute [local instance] referenceAddCommGroup referenceModule referenceSMul
attribute [local irreducible] referenceSubspace inclusion radiation covariant roughMultiply
  PauliFormLinear.form PauliGroundState.rawForm mass normSquared
  PauliGroundState.energy permutation waveLinear


theorem fermionic_character_iff (u : Ref N) : Fermionic u ↔
    ∀ π : Equiv.Perm (Fin N),
      permutation π u = PhysicalElectronicFermions.signCharacter N π • u :=
  (mem_sector_iff u).symm.trans
    (SignTwistedReduction.fixed_iff (G := Equiv.Perm (Fin N)) (Q := Ref N)
      (permutation (N := N)) (PhysicalElectronicFermions.signCharacter N)
      PhysicalFermionicAverage.sign_square u)

variable (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (F : Frame) (χ : ArticleCutoff)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

set_option maxHeartbeats 100000 in
theorem full_weak_of_fermionic {E : ℝ} {u : Ref N} (hu : Fermionic u)
    (hw : ∀ z : Ref N, Fermionic z → PauliGroundState.form C e F χ A v c hc z u =
      (E : ℂ) * mass z u) :
    IsWeakEigenstate (N := N) C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0) (profileBound F χ)
      (profile_bound (N := N) F χ 0) e (vector A) (positive v c) (negative v c)
      E u (physicalDomain (N := N) A v c hc u) := by
  let D := physicalDomain (N := N) A v c hc
  let q : Ref N →ₗ⋆[ℂ] Ref N →ₗ[ℂ] ℂ := PauliFormLinear.form (N := N) C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
    (profileBound F χ) (profile_bound (N := N) F χ 0) e (vector A) (positive v c) (negative v c) D
  have hq (z w : Ref N) : q z w = PauliGroundState.form C e F χ A v c hc z w :=
    PauliFormLinear.form_apply (N := N) C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0)
      (profileBound F χ) (profile_bound (N := N) F χ 0) e (vector A) (positive v c) (negative v c) D z w
  have hmass (π : Equiv.Perm (Fin N)) (z w : Ref N) :
      inner ℂ (E := PauliReference.Wave N) (waveLinear (permutation π z)) (waveLinear (permutation π w)) =
        inner ℂ (E := PauliReference.Wave N) (waveLinear z) (waveLinear w) :=
    (waveLinear_inner (permutation π z) (permutation π w)).trans
      ((congrArg₂ (mass (N := N)) (permutation_apply π z) (permutation_apply π w)).trans
        ((PauliPermutation.mass_permutation π z w).trans (waveLinear_inner z w).symm))
  have hinv (π : Equiv.Perm (Fin N)) (z w : Ref N) :
      q (permutation π z) (permutation π w) = q z w :=
    (hq _ _).trans ((congrArg₂ (PauliGroundState.form C e F χ A v c hc)
      (permutation_apply π z) (permutation_apply π w)).trans
      ((PauliPermutation.form_permutation C e F χ A v c hc π z w).trans (hq z w).symm))
  have hmul (π σ : Equiv.Perm (Fin N)) (z : Ref N) :
      permutation π (permutation σ z) = permutation (σ * π) z :=
    (permutation_apply π (permutation σ z)).trans
      ((congrArg (jointPermutation π) (permutation_apply σ z)).trans
        ((PauliPermutation.joint_mul π σ z).trans (permutation_apply (σ * π) z).symm))
  have huchar (π : Equiv.Perm (Fin N)) :
      permutation π u = PhysicalElectronicFermions.signCharacter N π • u :=
    (fermionic_character_iff u).mp hu π
  have hall := SignTwistedReduction.full_weak_of_fermionic_weak
    (G := Equiv.Perm (Fin N)) (Q := Ref N) (H := PauliReference.Wave N)
    permutation (PhysicalElectronicFermions.signCharacter N) hmul
    PhysicalFermionicAverage.sign_mul PhysicalFermionicAverage.sign_square
    PhysicalFermionicAverage.sign_star waveLinear hmass q hinv huchar E
    (fun z hz => (hq z u).trans
      ((hw z ((fermionic_character_iff z).mpr hz)).trans
        (congrArg (fun t : ℂ => (E : ℂ) * t) (waveLinear_inner z u).symm)))

  intro z hz
  exact (hq z u).symm.trans ((hall z).trans
    (congrArg (fun t : ℂ => (E : ℂ) * t) (waveLinear_inner z u)))

/-- A normalized variational ground state satisfies the actual Pauli
weak equation against every reference form vector, without a symmetry
restriction on the test. -/
theorem full_weak_equation (p : State N)
    (hp : IsGroundState C e F χ A v c hc p) :
    IsWeakEigenstate (N := N) C (profile (N := N) F χ 0) (profile_measurable (N := N) F χ 0) (profileBound F χ)
      (profile_bound (N := N) F χ 0) e (vector A) (positive v c) (negative v c)
      (energy C e F χ A v c hc p.vector) p.vector (physicalDomain (N := N) A v c hc p.vector) :=
  full_weak_of_fermionic C e F χ A v c hc p.fermionic
    (weak_equation C e F χ A v c hc p hp)

end PfHk.PauliGroundStateWeak

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
