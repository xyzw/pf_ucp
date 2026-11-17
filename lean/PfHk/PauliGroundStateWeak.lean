import PfHk.PauliFormLinear
import PfHk.FermionicVariational
import PfHk.SignTwistedReduction
import PfHk.PhysicalFermionicAverage

/-! The variational Pauli ground state satisfies the weak equation on
the actual joint position--spin antisymmetric reference sector. -/

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
local instance referenceAddCommGroup : AddCommGroup (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceAddCommGroup (N := N)
local instance referenceModule : Module ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceModule (N := N)
local instance referenceSMul : SMul ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceSMul (N := N)
attribute [local irreducible] referenceSubspace inclusion radiation covariant roughMultiply
  PauliFormLinear.form PauliGroundState.rawForm

def permutation (π : Equiv.Perm (Fin N)) : Ref N →ₗ[ℂ] Ref N where
  toFun := jointPermutation π
  map_add' u v := by
    funext s
    exact (PhysicalReferencePermutation.permutation π).map_add _ _
  map_smul' c u := by
    funext s
    exact (PhysicalReferencePermutation.permutation π).map_smul c _

theorem permutation_apply (π : Equiv.Perm (Fin N)) (u : Ref N) :
    permutation π u = jointPermutation π u := rfl

attribute [local irreducible] permutation

def sector : Submodule ℂ (Ref N) :=
  FiniteFormReduction.fixed
    (SignTwistedReduction.twist permutation (PhysicalElectronicFermions.signCharacter N))

theorem mem_sector_iff (u : Ref N) : u ∈ sector ↔ Fermionic u := by
  have h := SignTwistedReduction.fixed_iff permutation
    (PhysicalElectronicFermions.signCharacter N) PhysicalFermionicAverage.sign_square u
  constructor
  · intro hu π
    refine (permutation_apply π u).symm.trans ((h.mp hu π).trans ?_)
    funext s
    apply Subtype.ext
    rfl
  · intro hu
    apply h.mpr
    intro π
    refine (permutation_apply π u).trans ((hu π).trans ?_)
    funext s
    apply Subtype.ext
    rfl

attribute [local irreducible] sector

def waveLinear : Ref N →ₗ[ℂ] PauliReference.Wave N where
  toFun := PauliReference.wave
  map_add' u v := by
    have hc : (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) ((u + v) s)) =
        (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) +
          (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (v s)) := by
      funext s
      exact (inclusion (Fin N × Fin 3) (fun _ => 0)).map_add (u s) (v s)
    exact (congrArg (FiniteFiberL2.bundle (μ := volume)) hc).trans
      (FiniteFiberL2.bundle_add _ _)
  map_smul' c u := by
    have hc : (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) ((c • u) s)) =
        c • (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) := by
      funext s
      exact (inclusion (Fin N × Fin 3) (fun _ => 0)).map_smul c (u s)
    exact (congrArg (FiniteFiberL2.bundle (μ := volume)) hc).trans
      (FiniteFiberL2.bundle_smul c _)

theorem waveLinear_apply (u : Ref N) : waveLinear u = PauliReference.wave u := rfl

attribute [local irreducible] waveLinear

theorem waveLinear_injective : Function.Injective (waveLinear (N := N)) := by
  intro u v h
  exact PauliReference.wave_injective ((waveLinear_apply u).symm.trans (h.trans (waveLinear_apply v)))

theorem wave_inner (z u : Ref N) :
    inner ℂ (PauliReference.wave z) (PauliReference.wave u) = mass z u := by
  exact (FiniteFiberL2.isometry (S := SpinIndex N) (H := PhotonFock)
    (μ := volume)).inner_map_map
    (WithLp.toLp 2 (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (z s)))
    (WithLp.toLp 2 (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))

theorem waveLinear_inner (z u : Ref N) : inner ℂ (waveLinear z) (waveLinear u) = mass z u :=
  (congrArg₂ (inner ℂ) (waveLinear_apply z) (waveLinear_apply u)).trans (wave_inner z u)

theorem waveLinear_norm_sq (u : Ref N) : ‖waveLinear u‖ ^ 2 = normSquared u :=
  (congrArg (fun w : PauliReference.Wave N => ‖w‖ ^ 2) (waveLinear_apply u)).trans
    (PauliReference.wave_norm_sq u)

attribute [local irreducible] mass normSquared

variable (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (F : Frame) (χ : ArticleCutoff)

theorem energy_form (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (u : Ref N) : energy C e F χ A v c hc u = (PauliGroundState.form C e F χ A v c hc u u).re := rfl

attribute [local irreducible] PauliGroundState.energy

set_option maxHeartbeats 100000 in
theorem weak_equation (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (p : State N)
    (hp : IsGroundState C e F χ A v c hc p) :
    ∀ z : Ref N, Fermionic z →
      PauliGroundState.form C e F χ A v c hc z p.vector =
        (energy C e F χ A v c hc p.vector : ℂ) * mass z p.vector := by
  let D := physicalDomain (N := N) A v c hc
  let q : Ref N →ₗ⋆[ℂ] Ref N →ₗ[ℂ] ℂ := PauliFormLinear.form C (profile F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c) D
  have hq (z u : Ref N) : q z u = PauliGroundState.form C e F χ A v c hc z u :=
    PauliFormLinear.form_apply C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c) D z u
  have hmin : ∀ z ∈ (sector : Submodule ℂ (Ref N)), ‖waveLinear z‖ = 1 →
      energy C e F χ A v c hc p.vector ≤ (q z z).re := by
    intro z hz hn
    have hnormalized : normSquared z = 1 := by
      have hh := waveLinear_norm_sq z
      exact hh.symm.trans (by rw [hn, one_pow])
    let state : State N := ⟨z, hnormalized, (mem_sector_iff z).mp hz⟩
    have he : energy C e F χ A v c hc z = (q z z).re :=
      (energy_form C e F χ A v c hc z).trans (congrArg Complex.re (hq z z)).symm
    exact (hp state).trans_eq he
  have hnorm : ‖waveLinear p.vector‖ = 1 :=
    (congrArg norm (waveLinear_apply p.vector)).trans p.wave_norm
  have hE : (q p.vector p.vector).re = energy C e F χ A v c hc p.vector :=
    (congrArg Complex.re (hq p.vector p.vector)).trans
      (energy_form C e F χ A v c hc p.vector).symm
  have hw := FermionicVariational.weak_of_normalized_minimum
    (Q := Ref N) (H := PauliReference.Wave N)
    waveLinear waveLinear_injective q
    (PauliFormLinear.form_hermitian C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c) D) sector
    (u := p.vector) (E := energy C e F χ A v c hc p.vector)
    ((mem_sector_iff p.vector).mpr p.fermionic) hnorm hE hmin

  intro z hz
  exact (hq z p.vector).symm.trans ((hw z ((mem_sector_iff z).mpr hz)).trans
    (congrArg (fun t : ℂ => (energy C e F χ A v c hc p.vector : ℂ) * t)
      (waveLinear_inner z p.vector)))

end PfHk.PauliGroundStateWeak

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
