import GptLean.SymmetricLift.Induction
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
Completion of the recursively constructed block tensor families.

Completion is constructed with Mathlib's completion functor. Its operator-norm
continuity, smoothness, derivative, flatness and isometry are proved here.
Reindexing is supplied only as a fixed Hilbert-space isometry, with no smooth
lift or chart construction in that input.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.SymmetricLift

open UniformSpace
open scoped ContDiff

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

local instance completionRealH : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
local instance completionRealK : NormedSpace ℝ K := NormedSpace.restrictScalars ℝ ℂ K

theorem completion_finiteDimensional [FiniteDimensional ℂ H] :
    FiniteDimensional ℂ (Completion H) := by
  letI : CompleteSpace H := FiniteDimensional.complete ℂ H
  apply Module.Finite.of_surjective (Completion.toComplL : H →L[ℂ] Completion H).toLinearMap
  intro u
  have hc : IsClosed (Set.range ((↑) : H → Completion H)) :=
    (Completion.toComplₗᵢ : H →ₗᵢ[ℂ] Completion H).isometry.isClosedEmbedding.isClosed_range
  have hu := Completion.denseRange_coe (α := H) u
  rw [hc.closure_eq] at hu
  exact hu

theorem completion_norm_le (V : H →L[ℂ] K) :
    ‖(V.completion : Completion H →L[ℂ] Completion K)‖ ≤ ‖V‖ := by
  apply (V.completion : Completion H →L[ℂ] Completion K).opNorm_le_bound (norm_nonneg V)
  intro u
  induction u using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    simpa only [ContinuousLinearMap.completion_apply_coe, Completion.norm_coe] using V.le_opNorm u

theorem completion_add (V W : H →L[ℂ] K) :
    (V + W).completion = V.completion + W.completion := by
  ext u
  induction u using Completion.induction_on with
  | hp =>
    exact isClosed_eq (V + W).completion.continuous
      (V.completion.continuous.add W.completion.continuous)
  | ih u => simp only [ContinuousLinearMap.completion_apply_coe,
      ContinuousLinearMap.add_apply, Completion.coe_add]

theorem completion_smul (c : ℂ) (V : H →L[ℂ] K) :
    (c • V).completion = c • V.completion := by
  ext u
  induction u using Completion.induction_on with
  | hp =>
    exact isClosed_eq (c • V).completion.continuous
      (V.completion.continuous.const_smul c)
  | ih u => simp only [ContinuousLinearMap.completion_apply_coe,
      ContinuousLinearMap.smul_apply, Completion.coe_smul]

def completionLinear : (H →L[ℂ] K) →ₗ[ℂ] (Completion H →L[ℂ] Completion K) where
  toFun V := V.completion
  map_add' := completion_add
  map_smul' := completion_smul

/-- Completion is itself a bounded linear map of operator spaces. -/
def completionOperator : (H →L[ℂ] K) →L[ℂ] (Completion H →L[ℂ] Completion K) :=
  LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := H →L[ℂ] K) (F := Completion H →L[ℂ] Completion K)
    (completionLinear (H := H) (K := K)) 1
    (by
      refine fun (V : H →L[ℂ] K) => ?_
      change ‖(V.completion : Completion H →L[ℂ] Completion K)‖ ≤ 1 * ‖V‖
      simpa only [one_mul] using completion_norm_le (H := H) (K := K) V)

theorem completionOperator_apply (V : H →L[ℂ] K) : completionOperator V = V.completion := rfl

theorem completion_preserves_norm (V : H →L[ℂ] K) (hV : ∀ u, ‖V u‖ = ‖u‖)
    (u : Completion H) : ‖V.completion u‖ = ‖u‖ := by
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_norm
  | ih u => simp [ContinuousLinearMap.completion_apply_coe, hV]

theorem completion_preserves_flatness (V dV : H →L[ℂ] K)
    (hflat : ∀ u v, inner ℂ (V u) (dV v) = 0) (u v : Completion H) :
    inner ℂ (V.completion u) (dV.completion v) = 0 := by
  induction u, v using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) continuous_const
  | ih u v => simp [ContinuousLinearMap.completion_apply_coe, Completion.inner_coe, hflat]

theorem completion_comp {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J]
    (V : H →L[ℂ] K) (W : J →L[ℂ] H) :
    (V.comp W).completion = V.completion.comp W.completion := by
  ext u
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u => simp [ContinuousLinearMap.completion_apply_coe]

theorem completion_intertwines (V V' : H →L[ℂ] K) (R : H →L[ℂ] H)
    (h : ∀ u, V' (R u) = V u) (u : Completion H) :
    V'.completion (R.completion u) = V.completion u := by
  have he : V'.comp R = V := by ext z; exact h z
  rw [← ContinuousLinearMap.comp_apply, ← completion_comp, he]

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L]

local instance completionRealL : NormedSpace ℝ L := NormedSpace.restrictScalars ℝ ℂ L

/-- Completion followed by a fixed canonical tensor reindexing is a bounded
linear operation on the original operator space. -/
def transportCompleteOperator (e : L ≃ₗᵢ[ℂ] Completion H) :
    (H →L[ℂ] K) →L[ℂ] (L →L[ℂ] Completion K) :=
  ((ContinuousLinearMap.compL ℂ L (Completion H) (Completion K)).flip
    e.toLinearIsometry.toContinuousLinearMap).comp completionOperator

theorem transportCompleteOperator_apply (e : L ≃ₗᵢ[ℂ] Completion H)
    (V : H →L[ℂ] K) (u : L) :
    transportCompleteOperator e V u = V.completion (e u) := rfl

theorem transportCompleteOperator_norm (e : L ≃ₗᵢ[ℂ] Completion H)
    (V : H →L[ℂ] K) (hV : ∀ u, ‖V u‖ = ‖u‖) (u : L) :
    ‖transportCompleteOperator e V u‖ = ‖u‖ := by
  rw [transportCompleteOperator_apply, completion_preserves_norm V hV, e.norm_map]

theorem transportCompleteOperator_flat (e : L ≃ₗᵢ[ℂ] Completion H)
    (V dV : H →L[ℂ] K) (hflat : ∀ u v, inner ℂ (V u) (dV v) = 0)
    (u v : L) :
    inner ℂ (transportCompleteOperator e V u) (transportCompleteOperator e dV v) = 0 :=
  completion_preserves_flatness V dV hflat (e u) (e v)

/-- Permutation compatibility of a fixed reindexing transports the local
covariance identity. This hypothesis is solely an identity between tensor
representations, independent of the local family. -/
theorem transportCompleteOperator_equivariant (e : L ≃ₗᵢ[ℂ] Completion H)
    (V V' : H →L[ℂ] K) (R : H →L[ℂ] H) (S : L →L[ℂ] L)
    (he : ∀ u, e (S u) = R.completion (e u))
    (hV : ∀ u, V' (R u) = V u) (u : L) :
    transportCompleteOperator e V' (S u) = transportCompleteOperator e V u := by
  simp only [transportCompleteOperator_apply, he, completion_intertwines V V' R hV]

/-- Full symmetry implies block symmetry. Only this projection inclusion is
needed to transfer the constant action on the block-symmetric tensors. -/
theorem transportCompleteOperator_fixed (e : L ≃ₗᵢ[ℂ] Completion H)
    (V C : H →L[ℂ] K) (Q : H →L[ℂ] H) (P : L →L[ℂ] L)
    (he : ∀ u, Q.completion (e (P u)) = e (P u))
    (hV : ∀ z, V (Q z) = C z) (u : L) :
    transportCompleteOperator e V (P u) = transportCompleteOperator e C (P u) := by
  have h := completion_intertwines C V Q hV (e (P u))
  rw [he] at h
  exact h

/-- Metric estimates are unchanged on the pure tensor identified by the
canonical reindexing. -/
theorem transportCompleteOperator_metric (e : L ≃ₗᵢ[ℂ] Completion H)
    (dV : H →L[ℂ] K) (u : L) (z : H) (he : e u = (z : Completion H)) :
    ‖transportCompleteOperator e dV u‖ ^ 2 = ‖dV z‖ ^ 2 := by
  rw [transportCompleteOperator_apply, he, ContinuousLinearMap.completion_apply_coe,
    Completion.norm_coe]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem completion_contDiffOn {V : X → H →L[ℂ] K} {O : Set X}
    (hV : ContDiffOn ℝ ∞ V O) :
    ContDiffOn ℝ ∞ (fun x => (V x).completion) O := by
  have h : ContDiff ℝ ∞ (completionOperator (H := H) (K := K)) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℂ) (E := H →L[ℂ] K)
      (F := Completion H →L[ℂ] Completion K) (n := ∞) completionOperator).restrict_scalars ℝ
  exact h.comp_contDiffOn hV

theorem completion_hasFDerivAt {V : X → H →L[ℂ] K} {x : X}
    {dV : X →L[ℝ] (H →L[ℂ] K)} (hV : HasFDerivAt V dV x) :
    HasFDerivAt (fun y => (V y).completion)
      ((completionOperator (H := H) (K := K)).restrictScalars ℝ |>.comp dV) x := by
  have h : HasFDerivAt (completionOperator (H := H) (K := K))
      (completionOperator (H := H) (K := K)) (V x) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℂ) (E := H →L[ℂ] K)
      (F := Completion H →L[ℂ] Completion K) completionOperator
  have hr := HasFDerivAt.restrictScalars (𝕜' := ℂ)
    (E := H →L[ℂ] K) (F := Completion H →L[ℂ] Completion K) ℝ h
  exact hr.comp x hV

theorem transportCompleteOperator_contDiffOn (e : L ≃ₗᵢ[ℂ] Completion H)
    {V : X → H →L[ℂ] K} {O : Set X} (hV : ContDiffOn ℝ ∞ V O) :
    ContDiffOn ℝ ∞ (fun x => transportCompleteOperator e (V x)) O := by
  have h : ContDiff ℝ ∞ (transportCompleteOperator (K := K) e) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℂ) (E := H →L[ℂ] K)
      (F := L →L[ℂ] Completion K) (n := ∞) (transportCompleteOperator e)).restrict_scalars ℝ
  exact h.comp_contDiffOn hV

theorem transportCompleteOperator_hasFDerivAt (e : L ≃ₗᵢ[ℂ] Completion H)
    {V : X → H →L[ℂ] K} {x : X} {dV : X →L[ℝ] (H →L[ℂ] K)}
    (hV : HasFDerivAt V dV x) :
    HasFDerivAt (fun y => transportCompleteOperator e (V y))
      ((transportCompleteOperator (K := K) e).restrictScalars ℝ |>.comp dV) x := by
  have h : HasFDerivAt (transportCompleteOperator (K := K) e)
      (transportCompleteOperator (K := K) e) (V x) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℂ) (E := H →L[ℂ] K)
      (F := L →L[ℂ] Completion K) (transportCompleteOperator e)
  have hr := HasFDerivAt.restrictScalars (𝕜' := ℂ)
    (E := H →L[ℂ] K) (F := L →L[ℂ] Completion K) ℝ h
  exact hr.comp x hV

end GptLean.SymmetricLift
