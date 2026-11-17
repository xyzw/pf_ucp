import PfHk.PauliGroundState
import PfHk.PhysicalExternalFormLinear

/-! Sesquilinearity of the actual Pauli form, obtained from its finite
Pauli contractions and the already constructed scalar multiplier maps. -/

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

noncomputable section
namespace PfHk.PauliFormLinear

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.PauliSpin PfHk.PauliGroundState
  PfHk.PhysicalLocalEnergy PfHk.PhysicalExternalFormLinear

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

attribute [local irreducible] referenceSubspace inclusion covariant radiation roughMultiply

def component (s : SpinIndex N) : Ref N →ₗ[ℂ] Reference (Fin N × Fin 3) (fun _ => 0) :=
  LinearMap.proj s

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : (Fin N × Fin 3) → Configuration N → ℝ)
  (positive negative : Configuration N → ℝ)
  (D : ∀ u : Ref N, Domain A positive negative u)

/-- Each actual covariant derivative is a linear map on the finite-spin reference space. -/
def derivative (q : Fin N × Fin 3) (s : SpinIndex N) : Ref N →ₗ[ℂ] WaveSpace (Fin N × Fin 3) where
  toFun u := rawCovariant C κ hκ M hκbound e A positive negative u (D u) q s
  map_add' u v := by
    exact (covariantLinear (fun _ => 0) C κ hκ M hκbound e A positive negative
      (fun z => D (fun _ => z) s) q).map_add (u s) (v s)
  map_smul' c u := by
    exact (covariantLinear (fun _ => 0) C κ hκ M hκbound e A positive negative
      (fun z => D (fun _ => z) s) q).map_smul c (u s)

def contractionMap (n : Fin N) (s : SpinIndex N) : Ref N →ₗ[ℂ] WaveSpace (Fin N × Fin 3) :=
  ∑ a : Fin 3, sigmaFamily n a (derivative C κ hκ M hκbound e A positive negative D (n, a)) s

theorem contractionMap_apply (n : Fin N) (s : SpinIndex N) (u : Ref N) :
    contractionMap C κ hκ M hκbound e A positive negative D n s u =
      rawContraction C κ hκ M hκbound e A positive negative u (D u) n s := by
  simp only [contractionMap, LinearMap.sum_apply, rawContraction, PauliCurrentAlgebra.contraction,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  fin_cases a <;> simp [sigmaFamily, derivative]

def form : Ref N →ₗ⋆[ℂ] Ref N →ₗ[ℂ] ℂ :=
  (1 / 2 : ℂ) • ∑ n, ∑ s,
    innerForm (contractionMap C κ hκ M hκbound e A positive negative D n s) +
  ∑ s, innerForm ((radiation (Fin N × Fin 3) (fun _ => 0)).toLinearMap.comp (component s)) +
  ∑ s, innerForm ((roughLinear (fun _ => 0) positive
    (fun z => (D (fun _ => z) s).positive)).comp (component s)) -
  ∑ s, innerForm ((roughLinear (fun _ => 0) negative
    (fun z => (D (fun _ => z) s).negative)).comp (component s))

theorem form_apply (z u : Ref N) :
    form C κ hκ M hκbound e A positive negative D z u =
      rawForm C κ hκ M hκbound e A positive negative z u (D z) (D u) := by
  have hp (w : Ref N) (s : SpinIndex N) :
      roughLinear (fun _ => 0) positive (fun v => (D (fun _ => v) s).positive) (w s) =
        roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (w s)) (D w s).positive :=
    roughLinear_apply (fun _ => 0) positive _ (w s) (D w s).positive
  have hn (w : Ref N) (s : SpinIndex N) :
      roughLinear (fun _ => 0) negative (fun v => (D (fun _ => v) s).negative) (w s) =
        roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (w s)) (D w s).negative :=
    roughLinear_apply (fun _ => 0) negative _ (w s) (D w s).negative
  simp only [form, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, innerForm_apply, LinearMap.comp_apply, component, LinearMap.proj_apply,
    contractionMap_apply, hp, hn, rawForm, smul_eq_mul,
    ContinuousLinearMap.coe_coe]

attribute [local irreducible] form

theorem form_hermitian (z u : Ref N) :
    star (form C κ hκ M hκbound e A positive negative D z u) =
      form C κ hκ M hκbound e A positive negative D u z := by
  have hraw : star (rawForm C κ hκ M hκbound e A positive negative z u (D z) (D u)) =
      rawForm C κ hκ M hκbound e A positive negative u z (D u) (D z) := by
    change starRingEnd ℂ (rawForm C κ hκ M hκbound e A positive negative z u (D z) (D u)) = _
    simp only [rawForm, map_sub, map_add, map_mul, map_sum, inner_conj_symm,
      map_div₀, map_one, map_ofNat]
  exact (congrArg (star : ℂ → ℂ)
    (form_apply C κ hκ M hκbound e A positive negative D z u)).trans
      (hraw.trans (form_apply C κ hκ M hκbound e A positive negative D u z).symm)

end PfHk.PauliFormLinear

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
