import PfHk.PhysicalCommonFormDomain
import PfHk.CenteredPhysicalReference
import GptLean.PhysicalElectronicFermions

/-! The weak eigenvalue equation on the actual fermionic common form
subspace. Its tests are restricted by the existing electronic sign character.
The extension to arbitrary form tests is proved separately. -/

noncomputable section
namespace PfHk.PhysicalFermionicWeakEquation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.PhysicalPairDuality
  PfHk.CenteredPhysicalReference PfHk.PhysicalCommonFormDomain PfHk.PhysicalLocalEnergy

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] inclusion PhysicalPFReference.referenceSubspace externalForm

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

/-- Eigenstates of the restricted physical form are tested against exactly
its fermionic form vectors, with all multiplication domains constructed. -/
def IsFermionicWeakEigenstate (E : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) : Prop :=
  inclusion (Fin N × Fin 3) (fun _ => 0) u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock ∧
  ∀ z : Reference (Fin N × Fin 3) (fun _ => 0),
    inclusion (Fin N × Fin 3) (fun _ => 0) z ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock →
    externalForm (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e
      (vector A) (positive v c) (negative v c) z u
      (externalDomain A v c hc z) (externalDomain A v c hc u) =
      (E : ℂ) * inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) z)
        (inclusion (Fin N × Fin 3) (fun _ => 0) u)

end PfHk.PhysicalFermionicWeakEquation
