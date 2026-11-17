import PfHk.PhysicalFermionicAverage
import PfHk.PhysicalFermionicWeakEquation
import PfHk.PhysicalPermutationExternal
import PfHk.PhysicalExternalFormLinear

/-! The physical fermionic weak equation implies the full-space weak equation.
The common-domain memberships and all permutation invariances used by the
finite signed average are proved for the actual external potentials. -/

noncomputable section
namespace PfHk.PhysicalFermionicReduction

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.PhysicalPairDuality
  PfHk.CenteredPhysicalReference PfHk.PhysicalCommonFormDomain PfHk.PhysicalLocalEnergy
  PfHk.PhysicalFermionicWeakEquation PfHk.PhysicalFermionicAverage
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

attribute [local irreducible] inclusion PhysicalPFReference.referenceSubspace
  PhysicalExternalFormLinear.form externalForm

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

local instance referenceAddCommGroup : AddCommGroup (Ref N) :=
  PhysicalFermionicAverage.referenceAddCommGroup (N := N)

local instance referenceModule : Module ℂ (Ref N) :=
  PhysicalFermionicAverage.referenceModule (N := N)

/-- No extension to arbitrary tests is assumed. It follows by finite signed
averaging on the actual common reference domain. -/
theorem full_weak_of_fermionic_weak {E : ℝ} {u : Ref N}
    (hu : IsFermionicWeakEigenstate F χ C e A v c hc E u) :
    IsExternalWeakEigenstate (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
      E u (externalDomain A v c hc u) := by
  let D := externalDomain (N := N) A v c hc
  let L := (inclusion (Fin N × Fin 3) (fun _ => 0)).toLinearMap
  let q := PhysicalExternalFormLinear.form (fun _ => 0) C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
    (vector A) (positive v c) (negative v c) D
  have hq (z w : Ref N) : q z w =
      externalForm (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
        z w (D z) (D w) :=
    PhysicalExternalFormLinear.form_apply (fun _ => 0) C (profile F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
      (vector A) (positive v c) (negative v c) D z w (D z) (D w)
  have hinv (π : Perm N) (z w : Ref N) :
      q (PhysicalReferencePermutation.permutation π z)
        (PhysicalReferencePermutation.permutation π w) = q z w :=
    (hq _ _).trans ((PhysicalReferencePermutation.externalForm_permutation
      F χ C e A v c hc π z w).trans (hq z w).symm)
  have hall := SignTwistedReduction.full_weak_of_fermionic_weak
    (G := Perm N) (Q := Ref N) (H := WaveSpace (Fin N × Fin 3))
    (PhysicalReferencePermutation.permutation (N := N)) sign
    PhysicalReferencePermutation.permutation_permutation sign_mul sign_square sign_star
    L mass_permutation q hinv ((mem_fermionic_iff u).mp hu.1) E
    (fun z hz => (hq z u).trans (hu.2 z ((mem_fermionic_iff z).mpr hz)))
  intro z hz
  exact (hq z u).symm.trans (hall z)

end PfHk.PhysicalFermionicReduction
