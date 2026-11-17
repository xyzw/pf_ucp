import PfHk.PauliGroundState
import PfHk.PauliSpinMaps
import PfHk.PauliSpinPermutation
import PfHk.PhysicalPermutationExternal

/-! Joint position and spin permutations preserve the actual Pauli form.
This supplies the symmetry needed to extend fermionic weak equations to
arbitrary form-domain tests by finite signed averaging. -/

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

noncomputable section
namespace PfHk.PauliPermutation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PauliCurrentAlgebra
  PfHk.CenteredPhysicalReference PfHk.PhysicalCommonFormDomain PfHk.PhysicalLocalEnergy

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

variable {N : ℕ}

local instance pauliPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }
local instance pauliWaveDirectInner : InnerProductSpace ℂ (WaveSpace (Fin N × Fin 3)) :=
  { (inferInstance : InnerProductSpace ℂ (WaveSpace (Fin N × Fin 3))) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (WaveSpace (Fin N × Fin 3))) }
local instance referenceAddCommGroup : AddCommGroup (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceAddCommGroup (N := N)
local instance referenceModule : Module ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceModule (N := N)
local instance referenceSMul : SMul ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceSMul (N := N)
attribute [local irreducible] referenceSubspace inclusion radiation covariant roughMultiply
  externalCovariant rawCovariant rawContraction rawForm mass normSquared

abbrev pull (π : Equiv.Perm (Fin N)) := PhysicalReferencePermutation.pull (Q := PhotonFock) π

theorem joint_mul (π σ : Equiv.Perm (Fin N)) (u : Ref N) :
    jointPermutation π (jointPermutation σ u) = jointPermutation (σ * π) u := by
  funext s
  change PhysicalReferencePermutation.permutation π
    (PhysicalReferencePermutation.permutation σ (u (fun n => s (π.symm (σ.symm n))))) = _
  rw [PhysicalReferencePermutation.permutation_permutation]
  rfl

theorem mass_permutation (π : Equiv.Perm (Fin N)) (z u : Ref N) :
    mass (jointPermutation π z) (jointPermutation π u) = mass z u := by
  unfold mass
  calc
    _ = ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (z (reindex π.symm s)))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u (reindex π.symm s))) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact (congrArg₂ (fun a b : WaveSpace (Fin N × Fin 3) => inner ℂ (E := WaveSpace (Fin N × Fin 3)) a b)
        (PhysicalReferencePermutation.inclusion_permutation (N := N) π (z (reindex π.symm s)))
        (PhysicalReferencePermutation.inclusion_permutation (N := N) π (u (reindex π.symm s)))).trans
        ((pull π).inner_map_map _ _)
    _ = _ := Equiv.sum_comp (reindex π.symm) (fun s =>
      inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))

private theorem contraction_permute_map {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (π : Equiv.Perm (Fin N)) (L : H →ₗ[ℂ] K)
    (n : Fin N) (d : Fin 3 → SpinIndex N → H) :
    contraction n (fun a s => L (d a (reindex π.symm s))) =
      fun s => L (contraction (π n) d (reindex π.symm s)) := by
  funext s
  simp only [contraction, Finset.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hp : sigmaFamily n a (permuteFamily π.symm (d a)) =
      permuteFamily π.symm (sigmaFamily (π n) a (d a)) := by
    simpa only [π.symm_apply_apply] using sigmaFamily_permute π.symm (π n) a (d a)
  exact (congrFun (sigmaFamily_map n a L (permuteFamily π.symm (d a))) s).trans
    (congrArg L (congrFun hp s))

variable (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (F : Frame) (χ : ArticleCutoff)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

set_option hygiene false in
local notation "κ" => profile (N := N) F χ 0
set_option hygiene false in
local notation "hκ" => profile_measurable (N := N) F χ 0
set_option hygiene false in
local notation "M" => profileBound F χ
set_option hygiene false in
local notation "hb" => profile_bound (N := N) F χ 0
set_option hygiene false in
local notation "D" => physicalDomain (N := N) A v c hc

theorem covariant_permutation (π : Equiv.Perm (Fin N)) (u : Ref N)
    (q : Fin N × Fin 3) (s : SpinIndex N) :
    rawCovariant C κ hκ M hb e (vector A) (positive v c) (negative v c)
      (jointPermutation π u) (D (jointPermutation π u)) q s =
    pull π (rawCovariant C κ hκ M hb e (vector A) (positive v c) (negative v c)
      u (D u) (π q.1, q.2) (reindex π.symm s)) := by
  unfold rawCovariant
  exact PhysicalReferencePermutation.externalCovariant_permutation (N := N) F χ C e A v c
    (externalDomain (N := N) A v c hc) π (u (reindex π.symm s)) q

theorem contraction_permutation (π : Equiv.Perm (Fin N)) (u : Ref N) (n : Fin N) :
    rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c)
      (jointPermutation π u) (D (jointPermutation π u)) n =
    fun s => pull π (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c)
      u (D u) (π n) (reindex π.symm s)) := by
  unfold rawContraction
  have hd : (fun a => rawCovariant C κ hκ M hb e (vector A) (positive v c) (negative v c)
      (jointPermutation π u) (D (jointPermutation π u)) (n, a)) =
      fun a s => pull π (rawCovariant C κ hκ M hb e (vector A) (positive v c) (negative v c)
        u (D u) (π n, a) (reindex π.symm s)) := by
    funext a s
    exact covariant_permutation C e F χ A v c hc π u (n, a) s
  exact (congrArg (contraction (H := WaveSpace (Fin N × Fin 3)) n) hd).trans
    (contraction_permute_map (H := WaveSpace (Fin N × Fin 3))
      (K := WaveSpace (Fin N × Fin 3)) π (pull π).toLinearMap n _)

theorem kinetic_inner_permutation (π : Equiv.Perm (Fin N)) (z u : Ref N) :
    (∑ n, ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
      (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c)
        (jointPermutation π z) (D (jointPermutation π z)) n s)
      (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c)
        (jointPermutation π u) (D (jointPermutation π u)) n s)) =
    ∑ n, ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
      (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c) z (D z) n s)
      (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c) u (D u) n s) := by
  calc
    _ = ∑ n, ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c)
          z (D z) (π n) (reindex π.symm s))
        (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c)
          u (D u) (π n) (reindex π.symm s)) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro s hs
      exact (congrArg₂ (fun a b : WaveSpace (Fin N × Fin 3) => inner ℂ (E := WaveSpace (Fin N × Fin 3)) a b)
        (congrFun (contraction_permutation C e F χ A v c hc π z n) s)
        (congrFun (contraction_permutation C e F χ A v c hc π u n) s)).trans
        ((pull π).inner_map_map _ _)
    _ = ∑ n, ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c) z (D z) (π n) s)
        (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c) u (D u) (π n) s) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact Equiv.sum_comp (reindex π.symm) (fun s =>
        inner ℂ (E := WaveSpace (Fin N × Fin 3))
          (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c) z (D z) (π n) s)
          (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c) u (D u) (π n) s))
    _ = _ := Equiv.sum_comp π (fun n => ∑ s,
      inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c) z (D z) n s)
        (rawContraction C κ hκ M hb e (vector A) (positive v c) (negative v c) u (D u) n s))

theorem form_permutation (π : Equiv.Perm (Fin N)) (z u : Ref N) :
    PauliGroundState.form C e F χ A v c hc (jointPermutation π z) (jointPermutation π u) =
      PauliGroundState.form C e F χ A v c hc z u := by
  have hrad : (∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
      (radiation (Fin N × Fin 3) (fun _ => 0) (jointPermutation π z s))
      (radiation (Fin N × Fin 3) (fun _ => 0) (jointPermutation π u s))) =
      ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3)) (radiation (Fin N × Fin 3) (fun _ => 0) (z s))
        (radiation (Fin N × Fin 3) (fun _ => 0) (u s)) := by
    calc
      _ = ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
          (radiation (Fin N × Fin 3) (fun _ => 0) (z (reindex π.symm s)))
          (radiation (Fin N × Fin 3) (fun _ => 0) (u (reindex π.symm s))) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact PhysicalReferencePermutation.radiation_inner_permutation (N := N) π
          (z (reindex π.symm s)) (u (reindex π.symm s))
      _ = _ := Equiv.sum_comp (reindex π.symm) (fun s =>
        inner ℂ (E := WaveSpace (Fin N × Fin 3))
          (radiation (Fin N × Fin 3) (fun _ => 0) (z s))
          (radiation (Fin N × Fin 3) (fun _ => 0) (u s)))
  have hpos : (∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
      (roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (jointPermutation π z s))
        ((D (jointPermutation π z)) s).positive)
      (roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (jointPermutation π u s))
        ((D (jointPermutation π u)) s).positive)) =
      ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) ((D z) s).positive)
        (roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((D u) s).positive) := by
    calc
      _ = ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
          (roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (z (reindex π.symm s)))
            ((D z) (reindex π.symm s)).positive)
          (roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u (reindex π.symm s)))
            ((D u) (reindex π.symm s)).positive) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact (congrArg₂ (inner ℂ (E := WaveSpace (Fin N × Fin 3)))
          (PhysicalReferencePermutation.positive_multiplier_permutation (N := N) A v c
            (externalDomain (N := N) A v c hc) π (z (reindex π.symm s)))
          (PhysicalReferencePermutation.positive_multiplier_permutation (N := N) A v c
            (externalDomain (N := N) A v c hc) π (u (reindex π.symm s)))).trans
          ((pull π).inner_map_map _ _)
      _ = _ := Equiv.sum_comp (reindex π.symm) (fun s =>
        inner ℂ (E := WaveSpace (Fin N × Fin 3))
          (roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) ((D z) s).positive)
          (roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((D u) s).positive))
  have hneg : (∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
      (roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (jointPermutation π z s))
        ((D (jointPermutation π z)) s).negative)
      (roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (jointPermutation π u s))
        ((D (jointPermutation π u)) s).negative)) =
      ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) ((D z) s).negative)
        (roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((D u) s).negative) := by
    calc
      _ = ∑ s, inner ℂ (E := WaveSpace (Fin N × Fin 3))
          (roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (z (reindex π.symm s)))
            ((D z) (reindex π.symm s)).negative)
          (roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u (reindex π.symm s)))
            ((D u) (reindex π.symm s)).negative) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact (congrArg₂ (inner ℂ (E := WaveSpace (Fin N × Fin 3)))
          (PhysicalReferencePermutation.negative_multiplier_permutation (N := N) A v c
            (externalDomain (N := N) A v c hc) π (z (reindex π.symm s)))
          (PhysicalReferencePermutation.negative_multiplier_permutation (N := N) A v c
            (externalDomain (N := N) A v c hc) π (u (reindex π.symm s)))).trans
          ((pull π).inner_map_map _ _)
      _ = _ := Equiv.sum_comp (reindex π.symm) (fun s =>
        inner ℂ (E := WaveSpace (Fin N × Fin 3))
          (roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (z s)) ((D z) s).negative)
          (roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((D u) s).negative))
  unfold PauliGroundState.form rawForm
  exact congrArg₂ (fun a b : ℂ => a - b)
    (congrArg₂ (fun a b : ℂ => a + b)
      (congrArg₂ (fun a b : ℂ => a + b)
        (congrArg (fun a : ℂ => (1 / 2 : ℂ) * a)
          (kinetic_inner_permutation C e F χ A v c hc π z u)) hrad) hpos) hneg

end PfHk.PauliPermutation

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
