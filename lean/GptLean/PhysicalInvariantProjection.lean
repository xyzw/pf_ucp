import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
Orthogonal projection preserves a closed subspace when that subspace
reduces the unitary symmetries defining the projected fixed space. This
will pass support through the actual bosonic symmetrizer.
-/

noncomputable section

namespace GptLean.PhysicalInvariantProjection

open scoped InnerProductSpace

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A symmetric operator preserving a subspace commutes with its projection. -/
theorem symmetric_projection (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (A : H →L[ℂ] H) (hsym : ∀ u v, inner ℂ (A u) v = inner ℂ u (A v))
    (hinv : ∀ u ∈ S, A u ∈ S) (u : H) :
    S.starProjection (A u) = A (S.starProjection u) := by
  apply S.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hinv _ (S.starProjection_apply_mem u)
  · intro v hv
    rw [← map_sub, hsym]
    exact S.starProjection_inner_eq_zero u (A v) (hinv v hv)

/-- Unitary invariance in both directions gives projection covariance. -/
theorem unitary_projection (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (U : H ≃ₗᵢ[ℂ] H)
    (hU : ∀ u ∈ W, U u ∈ W) (hUinv : ∀ u ∈ W, U.symm u ∈ W) (u : H) :
    U (W.starProjection u) = W.starProjection (U u) := by
  symm
  apply W.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hU _ (W.starProjection_apply_mem u)
  · intro v hv
    rw [← map_sub]
    calc
      inner ℂ (U (u - W.starProjection u)) v =
          inner ℂ (U (u - W.starProjection u)) (U (U.symm v)) :=
        congrArg (inner ℂ (U (u - W.starProjection u))) (U.apply_symm_apply v).symm
      _ = inner ℂ (u - W.starProjection u) (U.symm v) := U.inner_map_map _ _
      _ = 0 := W.starProjection_inner_eq_zero u (U.symm v) (hUinv v hv)

/-- The orthogonal projection onto a unitary fixed space preserves reducing subspaces. -/
theorem fixed_projection_mem (S W : Submodule ℂ H)
    [S.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (U : ι → H ≃ₗᵢ[ℂ] H)
    (hS : ∀ u, u ∈ S ↔ ∀ i, U i u = u)
    (hU : ∀ i u, u ∈ W → U i u ∈ W)
    (hUinv : ∀ i u, u ∈ W → (U i).symm u ∈ W)
    {u : H} (hu : u ∈ W) : S.starProjection u ∈ W := by
  have hinv : ∀ v ∈ S, W.starProjection v ∈ S := by
    intro v hv
    apply (hS _).mpr
    intro i
    rw [unitary_projection W (U i) (hU i) (hUinv i), (hS v).mp hv i]
  have h := symmetric_projection S W.starProjection W.inner_starProjection_left_eq_right hinv u
  rw [W.starProjection_eq_self_iff.mpr hu] at h
  exact W.starProjection_eq_self_iff.mp h.symm

end GptLean.PhysicalInvariantProjection
