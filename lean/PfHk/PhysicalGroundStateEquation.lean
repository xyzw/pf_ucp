import PfHk.PhysicalGroundStateUCP

/-! The full weak equation on a specified common reference representative.
This lets two Hamiltonians be tested on exactly the same physical vector. -/

noncomputable section
namespace PfHk.PhysicalGroundStateEquation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.PhysicalDiamagneticPotential

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 150000

attribute [local irreducible] inclusion PhysicalPFReference.referenceSubspace
  IsExternalWeakEigenstate

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)

/-- Every reference representative of an existing variational ground state
satisfies the full weak equation with its actual ground-state energy. -/
theorem full_weak_equation (i : Fin N) (A : VectorPotential) (v : ScalarPotential)
    (p : State F χ C B S e (N := N))
    (hground : IsGroundState i F χ C B S e (shifted v A) p)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hvalue : inclusion (Fin N × Fin 3) (fun _ => 0) u = p.val) :
    IsExternalWeakEigenstate (fun _ => 0) C (CenteredPhysicalReference.profile F χ 0)
      (CenteredPhysicalReference.profile_measurable F χ 0)
      (CenteredPhysicalReference.profileBound F χ)
      (CenteredPhysicalReference.profile_bound F χ 0) e
      (vector A) (positive v 1) (negative v 1)
      (shiftedEnergy i F χ C B S e (shifted v A) p) u
      (externalDomain A v 1 zero_le_one u) := by
  have hex := PhysicalGroundStateUCP.exists_full_weak_eigenstate
    (N := N) F χ C B S e i A v p hground
  rcases hex with ⟨w, hw, heigen⟩
  have hwu : w = u := inclusion_injective (Fin N × Fin 3) (fun _ => 0)
    (hw.trans hvalue.symm)
  subst w
  exact heigen

end PfHk.PhysicalGroundStateEquation
