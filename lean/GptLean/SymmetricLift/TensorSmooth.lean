import GptLean.SymmetricLift.TensorProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
Operator-norm smooth tensorization of the local maps in Step 2.

The norm bound for Mathlib's Hilbert tensor product makes `mapL` a bounded
bilinear map. Its smoothness is derived here, rather than assumed for the
inductive tensor-product families.
-/

noncomputable section

namespace GptLean.SymmetricLift

open scoped ContDiff Topology

open scoped TensorProduct

variable {H K E F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Tensoring bounded operators is bounded bilinear in their operator norms. -/
theorem tensorMap_isBoundedBilinearMap :
    IsBoundedBilinearMap ℂ
      (fun p : (H →L[ℂ] K) × (E →L[ℂ] F) => TensorProduct.mapL p.1 p.2) where
  add_left := TensorProduct.mapL_add_left
  smul_left := TensorProduct.mapL_smul_left
  add_right := TensorProduct.mapL_add_right
  smul_right := TensorProduct.mapL_smul_right
  bound := ⟨1, zero_lt_one, fun f g => by
    simpa only [one_mul] using TensorProduct.norm_mapL_le f g⟩

variable [NormedSpace ℝ K] [IsScalarTower ℝ ℂ K]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

theorem tensorMap_contDiff :
    ContDiff ℝ ∞
      (fun p : (H →L[ℂ] K) × (E →L[ℂ] F) => TensorProduct.mapL p.1 p.2) := by
  have h : ContDiff ℂ ∞
      (fun p : (H →L[ℂ] K) × (E →L[ℂ] F) => TensorProduct.mapL p.1 p.2) :=
    tensorMap_isBoundedBilinearMap.contDiff
  exact h.restrict_scalars ℝ

/-- Smooth local isometry families tensor to a smooth operator-valued family. -/
theorem tensorMap_contDiffOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {O : Set X} {V : X → H →L[ℂ] K} {W : X → E →L[ℂ] F}
    (hV : ContDiffOn ℝ ∞ V O) (hW : ContDiffOn ℝ ∞ W O) :
    ContDiffOn ℝ ∞ (fun x => TensorProduct.mapL (V x) (W x)) O :=
  tensorMap_contDiff.comp₂_contDiffOn hV hW

/-- The genuine operator-valued derivative of the tensor family. -/
def tensorMapDerivative {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : H →L[ℂ] K) (W : E →L[ℂ] F)
    (dV : X →L[ℝ] (H →L[ℂ] K)) (dW : X →L[ℝ] (E →L[ℂ] F)) :
    X →L[ℝ] ((H ⊗[ℂ] E) →L[ℂ] (K ⊗[ℂ] F)) :=
  (IsBoundedBilinearMap.deriv (𝕜 := ℂ)
    (E := H →L[ℂ] K) (F := E →L[ℂ] F) (G := (H ⊗[ℂ] E) →L[ℂ] (K ⊗[ℂ] F))
    (tensorMap_isBoundedBilinearMap (H := H) (K := K) (E := E) (F := F)) (V, W)).restrictScalars ℝ |>.comp (dV.prod dW)

theorem tensorMapDerivative_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : H →L[ℂ] K) (W : E →L[ℂ] F)
    (dV : X →L[ℝ] (H →L[ℂ] K)) (dW : X →L[ℝ] (E →L[ℂ] F)) (d : X) :
    tensorMapDerivative V W dV dW d =
      TensorProduct.mapL V (dW d) + TensorProduct.mapL (dV d) W := rfl

theorem tensorMap_hasFDerivAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {V : X → H →L[ℂ] K} {W : X → E →L[ℂ] F} {x : X}
    {dV : X →L[ℝ] (H →L[ℂ] K)} {dW : X →L[ℝ] (E →L[ℂ] F)}
    (hV : HasFDerivAt V dV x) (hW : HasFDerivAt W dW x) :
    HasFDerivAt (fun y => TensorProduct.mapL (V y) (W y))
      (tensorMapDerivative (V x) (W x) dV dW) x := by
  exact ((IsBoundedBilinearMap.hasFDerivAt (𝕜 := ℂ)
    (E := H →L[ℂ] K) (F := E →L[ℂ] F) (G := (H ⊗[ℂ] E) →L[ℂ] (K ⊗[ℂ] F))
    (tensorMap_isBoundedBilinearMap (H := H) (K := K) (E := E) (F := F)) (V x, W x)).restrictScalars ℝ).comp x
    (hV.prodMk hW)

/-- The differentiated tensor family is flat when both factors are flat. -/
theorem tensorMapDerivative_flat {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : H →L[ℂ] K) (W : E →L[ℂ] F)
    (dV : X →L[ℝ] (H →L[ℂ] K)) (dW : X →L[ℝ] (E →L[ℂ] F))
    (hV : ∀ d u v, inner ℂ (V u) (dV d v) = 0)
    (hW : ∀ d u v, inner ℂ (W u) (dW d v) = 0)
    (d : X) (z w : H ⊗[ℂ] E) :
    inner ℂ (TensorProduct.mapL V W z) (tensorMapDerivative V W dV dW d w) = 0 := by
  rw [tensorMapDerivative_apply, ContinuousLinearMap.add_apply, add_comm]
  simpa only [TensorProduct.mapL_apply, LinearMap.add_apply] using
    tensorMap_flat V.toLinearMap (dV d).toLinearMap W.toLinearMap (dW d).toLinearMap
      (hV d) (hW d) z w

end GptLean.SymmetricLift
