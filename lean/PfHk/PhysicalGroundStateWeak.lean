import PfHk.FermionicVariational
import PfHk.PhysicalShiftedFormEnergy
import PfHk.PhysicalExternalFormLinear
import PfHk.PhysicalFermionicWeakEquation
import PfHk.PhysicalDiamagneticPotential
import GptLean.PhysicalGroundStateReversal

/-! The actual variational ground state satisfies the fermionic weak
equation. The input is the existing minimizer definition in gpt_lean.
No first-variation or weak-equation hypothesis is introduced.
-/

noncomputable section
namespace PfHk.PhysicalGroundStateWeak

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

local instance groundWeakPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

attribute [local irreducible] inclusion covariant radiation potential roughMultiply
  PhysicalPFReference.referenceSubspace

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)

set_option hygiene false in
local notation "Vp" => PhysicalRemoval.potential N 1
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
set_option hygiene false in
local notation "κF" => PhysicalRemovalKernels.full F χ N
set_option hygiene false in
local notation "hκF" => PhysicalRemovalKernels.full_measurable F χ N
set_option hygiene false in
local notation "hbF" => PhysicalRemovalKernels.full_bound F χ N

theorem profile_zero_eq_full :
    PfHk.CenteredPhysicalReference.profile (N := N) F χ 0 = PhysicalRemovalKernels.full F χ N := by
  funext i X
  simp only [PfHk.CenteredPhysicalReference.profile, zero_add]
  rfl

theorem profileBound_eq : PfHk.CenteredPhysicalReference.profileBound F χ =
    PhysicalRemovalKernels.bound F χ := rfl

private theorem externalForm_kernel_congr
    (κ κ' : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
    (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
    (hκ' : ∀ i, AEStronglyMeasurable (κ' i) volume)
    (M : ℝ) (hb : ∀ i, ∀ᵐ X ∂volume, ‖κ i X‖ ≤ M)
    (hb' : ∀ i, ∀ᵐ X ∂volume, ‖κ' i X‖ ≤ M) (h : κ = κ')
    (A : VectorPotential) (v : ScalarPotential)
    (u z : Reference (Fin N × Fin 3) (fun _ => 0)) :
    externalForm (fun _ => 0) C κ hκ M hb e (vector A) (positive v 1) (negative v 1)
      z u (externalDomain A v 1 zero_le_one z) (externalDomain A v 1 zero_le_one u) =
    externalForm (fun _ => 0) C κ' hκ' M hb' e (vector A) (positive v 1) (negative v 1)
      z u (externalDomain A v 1 zero_le_one z) (externalDomain A v 1 zero_le_one u) := by
  subst κ'
  rfl

def stateReference (p : State F χ C B S e (N := N)) :
    Reference (Fin N × Fin 3) (fun _ => 0) :=
  (PhysicalReferenceCoulombEquiv.equiv (N := N) 1 zero_le_one).symm
    (PhysicalGroundState.stateVector F χ C B S e p)

theorem stateReference_value (p : State F χ C B S e (N := N)) :
    inclusion (Fin N × Fin 3) (fun _ => 0) (stateReference F χ C B S e p) = p.val :=
  (PhysicalReferenceCoulombEquiv.inclusion_symm (N := N) 1 zero_le_one
    (PhysicalGroundState.stateVector F χ C B S e p)).trans
      (PhysicalGroundState.stateVector_spec F χ C B S e p)

theorem stateReference_fermionic (p : State F χ C B S e (N := N)) :
    inclusion (Fin N × Fin 3) (fun _ => 0) (stateReference F χ C B S e p) ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
  (congrArg (fun ψ : WaveSpace (Fin N × Fin 3) =>
    ψ ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
      (stateReference_value F χ C B S e p)).mpr
        (TransformationsPureStates.pure_fermionic Vp C Kf hKf MK hMK B S e p)

theorem pure_density_eq_pair (i : Fin N) (p : State F χ C B S e (N := N))
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hvalue : inclusion (Fin N × Fin 3) (fun _ => 0) u = p.val) :
    (PhysicalGroundState.model i F χ C B S e).density p =
      PhysicalPFParticle.pair (N := N) C Kf hKf MK hMK (fun _ => 0) i e u := by
  let uc := PhysicalReferenceCoulombEquiv.equiv (N := N) 1 zero_le_one u
  have huc : inclusion (Fin N × Fin 3) Vp uc = p.val :=
    (PhysicalReferenceCoulombEquiv.inclusion_equiv (N := N) 1 zero_le_one u).trans hvalue
  exact (TransformationsPureStates.pure_density Vp C Kf hKf MK hMK B S e i p uc huc).trans
    (PhysicalShiftedFormEnergy.pair_equiv (N := N) C Kf hKf MK hMK e i 1 zero_le_one u)

theorem shiftedEnergy_eq_externalEnergy (i : Fin N) (A : VectorPotential) (v w : ScalarPotential)
    (hshift : (w.val : PhysicalSourceCoordinates.Position → ℝ) =ᵐ[volume]
      fun x => v.val x + (1 / 2 : ℝ) * ∑ b : Fin 3, A.val x b ^ 2)
    (p : State F χ C B S e (N := N))
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hvalue : inclusion (Fin N × Fin 3) (fun _ => 0) u = p.val) :
    shiftedEnergy i F χ C B S e (w, A) p =
      externalEnergy (fun _ => 0) C κF hκF MK hbF e
        (vector A) (positive v 1) (negative v 1) u (externalDomain A v 1 zero_le_one u) := by
  let uc := PhysicalReferenceCoulombEquiv.equiv (N := N) 1 zero_le_one u
  have huc : inclusion (Fin N × Fin 3) Vp uc = p.val :=
    (PhysicalReferenceCoulombEquiv.inclusion_equiv (N := N) 1 zero_le_one u).trans hvalue
  have hferm : inclusion (Fin N × Fin 3) (fun _ => 0) u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
    (congrArg (fun ψ : WaveSpace (Fin N × Fin 3) =>
      ψ ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock) hvalue).mpr
        (TransformationsPureStates.pure_fermionic Vp C Kf hKf MK hMK B S e p)
  have he := TransformationsPureStates.pure_energy Vp C Kf hKf MK hMK B S e i p uc huc
  have hp := pure_density_eq_pair F χ C B S e i p u hvalue
  exact (congrArg₂ (· + ·) he (congrArg (pairPotential (w, A)) hp)).trans
    (PhysicalShiftedFormEnergy.external_energy_eq_shifted_pair (N := N) C Kf hKf MK hMK e i A v w
      hshift 1 zero_le_one u hferm).symm

attribute [local irreducible] PhysicalExternalFormLinear.form externalForm
  stateReference PhysicalReferenceCoulombEquiv.equiv

local instance referenceAddCommGroup : AddCommGroup (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  (PhysicalPFReference.referenceSubspace (Fin N × Fin 3) (fun _ => 0)).addCommGroup

local instance referenceModule : Module ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  (PhysicalPFReference.referenceSubspace (Fin N × Fin 3) (fun _ => 0)).module

theorem weak_equation (i : Fin N) (A : VectorPotential) (v w : ScalarPotential)
    (hshift : (w.val : PhysicalSourceCoordinates.Position → ℝ) =ᵐ[volume]
      fun x => v.val x + (1 / 2 : ℝ) * ∑ b : Fin 3, A.val x b ^ 2)
    (p : State F χ C B S e (N := N))
    (hground : IsGroundState i F χ C B S e (w, A) p) :
    ∀ z : Reference (Fin N × Fin 3) (fun _ => 0),
      inclusion (Fin N × Fin 3) (fun _ => 0) z ∈
        PhysicalElectronicFermions.fermionicSubspace N PhotonFock →
      externalForm (fun _ => 0) C κF hκF MK hbF e
        (vector A) (positive v 1) (negative v 1) z (stateReference F χ C B S e p)
        (externalDomain A v 1 zero_le_one z)
        (externalDomain A v 1 zero_le_one (stateReference F χ C B S e p)) =
      (shiftedEnergy i F χ C B S e (w, A) p : ℂ) *
        ⟪inclusion (Fin N × Fin 3) (fun _ => 0) z,
          inclusion (Fin N × Fin 3) (fun _ => 0) (stateReference F χ C B S e p)⟫_ℂ := by
  let L := (inclusion (Fin N × Fin 3) (fun _ => 0)).toLinearMap
  let D := externalDomain (N := N) A v 1 zero_le_one
  let q := PhysicalExternalFormLinear.form (fun _ => 0) C κF hκF MK hbF e
    (vector A) (positive v 1) (negative v 1) D
  let sector : Submodule ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
    (PhysicalElectronicFermions.fermionicSubspace N PhotonFock).comap L
  let u := stateReference F χ C B S e p
  let E := shiftedEnergy i F χ C B S e (w, A) p
  have hdiag (z : Reference (Fin N × Fin 3) (fun _ => 0)) :
      (q z z).re = externalEnergy (fun _ => 0) C κF hκF MK hbF e
        (vector A) (positive v 1) (negative v 1) z (D z) :=
    (congrArg Complex.re (PhysicalExternalFormLinear.form_apply (fun _ => 0) C κF hκF MK hbF e
      (vector A) (positive v 1) (negative v 1) D z z (D z) (D z))).trans
        (externalForm_diagonal (fun _ => 0) C κF hκF MK hbF e
          (vector A) (positive v 1) (negative v 1) z (D z))
  have hE : (q u u).re = E := (hdiag u).trans
    (shiftedEnergy_eq_externalEnergy F χ C B S e i A v w hshift p u
      (stateReference_value F χ C B S e p)).symm
  have hnorm : ‖L u‖ = 1 :=
    (congrArg norm (stateReference_value F χ C B S e p)).trans p.property.1
  have hmin : ∀ z ∈ sector, ‖L z‖ = 1 → E ≤ (q z z).re := by
    intro z hz hn
    let pc := TransformationsPureStates.ofVector Vp C Kf hKf MK hMK B S e
      (L z) hn hz ⟨PhysicalReferenceCoulombEquiv.equiv (N := N) 1 zero_le_one z,
        PhysicalReferenceCoulombEquiv.inclusion_equiv (N := N) 1 zero_le_one z⟩
    have hg := hground pc
    exact hg.trans_eq ((shiftedEnergy_eq_externalEnergy F χ C B S e i A v w hshift pc z rfl).trans
      (hdiag z).symm)
  have hL : Function.Injective L := inclusion_injective (Fin N × Fin 3) (fun _ => 0)
  have hq : ∀ x y, star (q x y) = q y x :=
    PhysicalExternalFormLinear.form_hermitian (fun _ => 0) C κF hκF MK hbF e
      (vector A) (positive v 1) (negative v 1) D
  have hsector : u ∈ sector := stateReference_fermionic F χ C B S e p
  have hweak : ∀ z ∈ sector, q z u = (E : ℂ) * ⟪L z, L u⟫_ℂ :=
    FermionicVariational.weak_of_normalized_minimum
      (Q := Reference (Fin N × Fin 3) (fun _ => 0))
      (H := WaveSpace (Fin N × Fin 3)) L hL q hq sector
      (u := u) (E := E) hsector hnorm hE hmin
  intro z hz
  exact (PhysicalExternalFormLinear.form_apply (fun _ => 0) C κF hκF MK hbF e
    (vector A) (positive v 1) (negative v 1) D z u (D z) (D u)).symm.trans (hweak z hz)

/-- The existing variational ground state has an actual free reference
representative satisfying the fermionic weak eigenvalue equation. -/
theorem exists_weak_eigenstate (i : Fin N) (A : VectorPotential) (v w : ScalarPotential)
    (hshift : (w.val : PhysicalSourceCoordinates.Position → ℝ) =ᵐ[volume]
      fun x => v.val x + (1 / 2 : ℝ) * ∑ b : Fin 3, A.val x b ^ 2)
    (p : State F χ C B S e (N := N))
    (hground : IsGroundState i F χ C B S e (w, A) p) :
    ∃ u : Reference (Fin N × Fin 3) (fun _ => 0),
      inclusion (Fin N × Fin 3) (fun _ => 0) u = p.val ∧
      PhysicalFermionicWeakEquation.IsFermionicWeakEigenstate F χ C e A v 1 zero_le_one
        (shiftedEnergy i F χ C B S e (w, A) p) u := by
  refine ⟨stateReference F χ C B S e p, stateReference_value F χ C B S e p,
    stateReference_fermionic F χ C B S e p, ?_⟩
  intro z hz
  exact (externalForm_kernel_congr (N := N) C e
    (PfHk.CenteredPhysicalReference.profile (N := N) F χ 0) κF
    (PfHk.CenteredPhysicalReference.profile_measurable (N := N) F χ 0) hκF MK
    (PfHk.CenteredPhysicalReference.profile_bound (N := N) F χ 0) hbF
    (profile_zero_eq_full (N := N) F χ)
    A v (stateReference F χ C B S e p) z).trans
      (weak_equation F χ C B S e i A v w hshift p hground z hz)

/-- The diamagnetic shift is constructed in the actual scalar potential
space, so the variational-to-weak bridge needs no representation premise. -/
theorem exists_shifted_weak_eigenstate (i : Fin N) (A : VectorPotential)
    (v : ScalarPotential) (p : State F χ C B S e (N := N))
    (hground : IsGroundState i F χ C B S e
      (PhysicalDiamagneticPotential.shifted v A) p) :
    ∃ u : Reference (Fin N × Fin 3) (fun _ => 0),
      inclusion (Fin N × Fin 3) (fun _ => 0) u = p.val ∧
      PhysicalFermionicWeakEquation.IsFermionicWeakEigenstate F χ C e A v 1 zero_le_one
        (shiftedEnergy i F χ C B S e (PhysicalDiamagneticPotential.shifted v A) p) u :=
  exists_weak_eigenstate F χ C B S e i A v
    (PhysicalDiamagneticPotential.shifted v A).1
    (PhysicalDiamagneticPotential.shifted_scalar_sum_ae v A) p hground

end PfHk.PhysicalGroundStateWeak
