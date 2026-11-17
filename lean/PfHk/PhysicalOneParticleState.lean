import PfHk.PhysicalGroundStateWeak
import GptLean.PhysicalElectronicVacuumGraph

/-! One-particle reference vectors give actual normalized physical states.
For a single electron the fermionic constraint is automatic. -/

noncomputable section
namespace PfHk.PhysicalOneParticleState

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms GptLean.SymmetricLift

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

abbrev Index := Fin 1 × Fin 3
abbrev Ref := Reference Index (fun _ => 0)

/-- There is no nontrivial electronic permutation for one particle. -/
theorem fermionic (ψ : WaveSpace Index) :
    ψ ∈ PhysicalElectronicFermions.fermionicSubspace 1 PhotonFock := by
  apply (PhysicalElectronicFermions.mem_fermionicSubspace_iff 1 PhotonFock ψ).mpr
  intro π
  have hπ : π = 1 := Subsingleton.elim _ _
  subst π
  exact Filter.Eventually.of_forall fun X => by
    simp [PhysicalElectronicFermions.signCharacter]

theorem coulomb_potential_one :
    PhysicalRemoval.potential 1 1 = (fun _ : Position Index => 0) := by
  funext X
  simp [PhysicalRemoval.potential, PhysicalCoulombH1.potential]

variable (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)

set_option hygiene false in
local notation "Vp" => PhysicalRemoval.potential 1 1
set_option hygiene false in
local notation "Kf" => PhysicalProfiles.momentumKernel (formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "hKf" => PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "MK" => PhysicalRemovalKernels.bound F χ
set_option hygiene false in
local notation "hMK" => PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)

/-- A normalized reference vector determines a state in the original
Pauli--Fierz model, without a photon-number restriction. -/
def ofReference (u : Ref) (hu : ‖inclusion Index (fun _ => 0) u‖ = 1) :
    State F χ C B S e (N := 1) :=
  TransformationsPureStates.ofVector Vp C Kf hKf MK hMK B S e
    (inclusion Index (fun _ => 0) u) hu (fermionic _)
    ⟨PhysicalReferenceCoulombEquiv.equiv (N := 1) 1 zero_le_one u,
      PhysicalReferenceCoulombEquiv.inclusion_equiv (N := 1) 1 zero_le_one u⟩

theorem ofReference_value (u : Ref) (hu : ‖inclusion Index (fun _ => 0) u‖ = 1) :
    (ofReference F χ C B S e u hu).val = inclusion Index (fun _ => 0) u := rfl

theorem stateReference_ofReference (u : Ref)
    (hu : ‖inclusion Index (fun _ => 0) u‖ = 1) :
    PhysicalGroundStateWeak.stateReference F χ C B S e
      (ofReference F χ C B S e u hu) = u := by
  apply inclusion_injective Index (fun _ => 0)
  exact PhysicalGroundStateWeak.stateReference_value F χ C B S e _

end PfHk.PhysicalOneParticleState
