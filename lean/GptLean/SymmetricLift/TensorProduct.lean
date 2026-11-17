import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
Tensor-product algebra in Step 2 of the symmetric-tensor appendix.

These theorems use Mathlib's inner-product tensor product itself. They
prove closure of flatness and fixed projected subspaces under tensor
products, and the connection and metric identities for a derivative
acting on one unit tensor factor. Completion and Sobolev product rules
remain standard analytic inputs.
-/

noncomputable section

namespace GptLean.SymmetricLift

open scoped TensorProduct

variable {H K E F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The product rule for two flat chart isometries stays flat. -/
theorem tensorMap_flat (V dV : H →ₗ[ℂ] K) (W dW : E →ₗ[ℂ] F)
    (hV : ∀ x y, inner ℂ (V x) (dV y) = 0)
    (hW : ∀ x y, inner ℂ (W x) (dW y) = 0)
    (z w : H ⊗[ℂ] E) :
    inner ℂ (TensorProduct.map V W z)
      ((TensorProduct.map dV W + TensorProduct.map V dW) w) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y' =>
      simp only [LinearMap.add_apply, TensorProduct.map_tmul, inner_add_right,
        TensorProduct.inner_tmul, hV, hW, zero_mul, mul_zero, add_zero]
    | add z z' hz hz' => simp only [map_add, inner_add_right, hz, hz', add_zero]
  | add z z' hz hz' => simp only [map_add, inner_add_left, hz, hz', add_zero]

/-- If each derivative kills its fixed projected part, so does the product derivative. -/
theorem tensorMap_derivative_fixed (P : H →ₗ[ℂ] H) (Q : E →ₗ[ℂ] E)
    (V dV : H →ₗ[ℂ] K) (W dW : E →ₗ[ℂ] F)
    (hV : ∀ x, dV (P x) = 0) (hW : ∀ y, dW (Q y) = 0)
    (z : H ⊗[ℂ] E) :
    (TensorProduct.map dV W + TensorProduct.map V dW) (TensorProduct.map P Q z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [hV, hW]
  | add z z' hz hz' => simp only [map_add, hz, hz', add_zero]

/-- The constant action on each projected subspace tensorizes. -/
theorem tensorMap_fixed (P : H →ₗ[ℂ] H) (Q : E →ₗ[ℂ] E)
    (V C : H →ₗ[ℂ] K) (W D : E →ₗ[ℂ] F)
    (hV : ∀ x, V (P x) = C x) (hW : ∀ y, W (Q y) = D y)
    (z : H ⊗[ℂ] E) :
    TensorProduct.map V W (TensorProduct.map P Q z) = TensorProduct.map C D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [hV, hW]
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- A derivative of one factor sees precisely that factor's connection. -/
theorem tensor_connection_left (u du : H) (v : E) (hv : ‖v‖ = 1) :
    inner ℂ (u ⊗ₜ[ℂ] v) (du ⊗ₜ[ℂ] v) = inner ℂ u du := by
  simp [TensorProduct.inner_tmul, inner_self_eq_norm_sq_to_K, hv]

theorem tensor_connection_right (u : H) (v dv : E) (hu : ‖u‖ = 1) :
    inner ℂ (u ⊗ₜ[ℂ] v) (u ⊗ₜ[ℂ] dv) = inner ℂ v dv := by
  simp [TensorProduct.inner_tmul, inner_self_eq_norm_sq_to_K, hu]

/-- The other unit factors contribute no multiplier to the derivative metric. -/
theorem tensor_metric_left (du : H) (v : E) (hv : ‖v‖ = 1) :
    ‖du ⊗ₜ[ℂ] v‖ ^ 2 = ‖du‖ ^ 2 := by simp [hv]

theorem tensor_metric_right (u : H) (dv : E) (hu : ‖u‖ = 1) :
    ‖u ⊗ₜ[ℂ] dv‖ ^ 2 = ‖dv‖ ^ 2 := by simp [hu]

/-- The two-factor telescoping estimate used to compare a product with its diagonal tensor. -/
theorem tensor_telescope (u u₀ : H) (v v₀ : E)
    (hu : ‖u₀‖ = 1) (hv : ‖v‖ = 1) :
    ‖u ⊗ₜ[ℂ] v - u₀ ⊗ₜ[ℂ] v₀‖ ≤ ‖u - u₀‖ + ‖v - v₀‖ := by
  have hsplit : u ⊗ₜ[ℂ] v - u₀ ⊗ₜ[ℂ] v₀ =
      (u - u₀) ⊗ₜ[ℂ] v + u₀ ⊗ₜ[ℂ] (v - v₀) := by
    simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  rw [hsplit]
  calc
    ‖(u - u₀) ⊗ₜ[ℂ] v + u₀ ⊗ₜ[ℂ] (v - v₀)‖ ≤
        ‖(u - u₀) ⊗ₜ[ℂ] v‖ + ‖u₀ ⊗ₜ[ℂ] (v - v₀)‖ := norm_add_le _ _
    _ = ‖u - u₀‖ + ‖v - v₀‖ := by simp [hu, hv]

end GptLean.SymmetricLift
