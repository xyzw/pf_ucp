import GptLean.PhysicalFockSeparable
import GptLean.PhysicalL2Countable
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
The environmental coordinates of the physical Fock tensor product.

The coefficient map is constructed from an actual Hilbert basis of the
discarded photon Fock space. Its isometry and bounded-observable identity
follow from tensor-product density and Parseval. They are not assumptions
about the localization channel.
-/

noncomputable section

namespace GptLean.PhysicalFock.TensorCoordinates

open UniformSpace Filter Topology
open scoped ENNReal InnerProductSpace TensorProduct

variable {H K ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev TensorSpace (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] := Completion (TensorProduct ℂ H K)

/-- The ordinary completed Hilbert tensor product, bilinear in its inputs. -/
def tensor : H →L[ℂ] K →L[ℂ] TensorSpace H K :=
  (ContinuousLinearMap.compL ℂ K (TensorProduct ℂ H K) (TensorSpace H K)
    Completion.toComplL).comp (TensorProduct.mkL ℂ H K)

@[simp] theorem tensor_apply (v : H) (w : K) :
    tensor v w = ((v ⊗ₜ[ℂ] w : TensorProduct ℂ H K) : TensorSpace H K) := rfl

theorem tensor_inner (v v' : H) (w w' : K) :
    ⟪tensor v w, tensor v' w'⟫_ℂ = ⟪v, v'⟫_ℂ * ⟪w, w'⟫_ℂ := by
  rw [tensor_apply, tensor_apply, Completion.inner_coe, TensorProduct.inner_tmul]

variable (b : HilbertBasis ι ℂ K)

def insertion (i : ι) : H →ₗᵢ[ℂ] TensorSpace H K :=
  (tensor.flip (b i)).toLinearMap.isometryOfInner (fun v w => by
    change ⟪tensor v (b i), tensor w (b i)⟫_ℂ = _
    rw [tensor_inner, inner_self_eq_one_of_norm_eq_one (b.orthonormal.norm_eq_one i), mul_one])

@[simp] theorem insertion_apply (i : ι) (v : H) : insertion (H := H) b i v = tensor v (b i) := rfl

theorem insertion_orthogonal : OrthogonalFamily ℂ (fun _ : ι => H) (insertion b) := by
  intro i j hij v w
  rw [insertion_apply, insertion_apply, tensor_inner, b.orthonormal.2 hij, mul_zero]

private theorem tensor_mem_spanClosure (v : H) (w : K) :
    tensor v w ∈ (⨆ i, LinearMap.range (insertion (H := H) b i).toLinearMap).topologicalClosure := by
  have hs := (tensor v).hasSum (b.hasSum_repr w)
  change tensor v w ∈ closure ((⨆ i, LinearMap.range
    (insertion (H := H) b i).toLinearMap : Submodule ℂ (TensorSpace H K)) : Set (TensorSpace H K))
  apply mem_closure_of_tendsto hs
  apply Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  exact Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self (insertion (H := H) b i).toLinearMap v)

/-- Finite tensors are dense, and the environmental basis expands their second factor. -/
theorem insertion_total :
    ⊤ ≤ (⨆ i, LinearMap.range (insertion (H := H) b i).toLinearMap).topologicalClosure := by
  intro u hu
  clear hu
  induction u using Completion.induction_on with
  | hp =>
    exact Submodule.isClosed_topologicalClosure
      (⨆ i, LinearMap.range (insertion (H := H) b i).toLinearMap)
  | ih u =>
    induction u using TensorProduct.induction_on with
    | zero =>
      rw [Completion.coe_zero]
      exact Submodule.zero_mem _
    | tmul v w => exact tensor_mem_spanClosure b v w
    | add u v hu hv => simpa only [Completion.coe_add] using Submodule.add_mem _ hu hv

variable [CompleteSpace H]

def coefficients : TensorSpace H K ≃ₗᵢ[ℂ] lp (fun _ : ι => H) 2 :=
  (IsHilbertSum.mk (insertion_orthogonal (H := H) b) (insertion_total (H := H) b)).linearIsometryEquiv

theorem coefficients_inner (u : TensorSpace H K) (i : ι) (v : H) :
    ⟪v, coefficients b u i⟫_ℂ = ⟪tensor v (b i), u⟫_ℂ := by
  classical
  rw [← lp.inner_single_left i v (coefficients b u),
    ← (coefficients b).symm.inner_map_map (lp.single 2 i v) (coefficients b u),
    LinearIsometryEquiv.symm_apply_apply]
  change ⟪(IsHilbertSum.mk (insertion_orthogonal b) (insertion_total b)).linearIsometryEquiv.symm
    (lp.single 2 i v), u⟫_ℂ = _
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply_single, insertion_apply]

theorem coefficients_tensor (v : H) (w : K) (i : ι) :
    coefficients b (tensor v w) i = ⟪b i, w⟫_ℂ • v := by
  apply ext_inner_left ℂ
  intro z
  rw [coefficients_inner, tensor_inner, inner_smul_right]
  ring

/-- Every bounded operator on the retained factor acts on the genuine completed tensor product. -/
def retainedOperator (A : H →L[ℂ] H) : TensorSpace H K →L[ℂ] TensorSpace H K :=
  (A.rTensor K).completion

omit [CompleteSpace H] in
theorem retainedOperator_tensor (A : H →L[ℂ] H) (v : H) (w : K) :
    retainedOperator (K := K) A (tensor v w) = tensor (A v) w := by
  rw [tensor_apply, retainedOperator, ContinuousLinearMap.completion_apply_coe]
  rfl

private theorem tensor_inner_retainedOperator (A : H →L[ℂ] H) (v : H) (w : K)
    (u : TensorSpace H K) :
    ⟪tensor v w, retainedOperator A u⟫_ℂ = ⟪tensor (A.adjoint v) w, u⟫_ℂ := by
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u =>
    induction u using TensorProduct.induction_on with
    | zero => rw [Completion.coe_zero, map_zero, inner_zero_right, inner_zero_right]
    | tmul x y =>
      change ⟪tensor v w, retainedOperator A (tensor x y)⟫_ℂ =
        ⟪tensor (A.adjoint v) w, tensor x y⟫_ℂ
      rw [retainedOperator_tensor, tensor_inner, tensor_inner, A.adjoint_inner_left]
    | add u z hu hz =>
      simpa only [Completion.coe_add, map_add, inner_add_right] using congrArg₂ (· + ·) hu hz

theorem coefficients_retainedOperator (A : H →L[ℂ] H) (u : TensorSpace H K) (i : ι) :
    coefficients b (retainedOperator A u) i = A (coefficients b u i) := by
  apply ext_inner_left ℂ
  intro v
  rw [coefficients_inner, tensor_inner_retainedOperator, ← coefficients_inner, A.adjoint_inner_left]

theorem coefficients_observable_hasSum (A : H →L[ℂ] H) (u : TensorSpace H K) :
    HasSum (fun i => ⟪coefficients b u i, A (coefficients b u i)⟫_ℂ)
      ⟪u, retainedOperator A u⟫_ℂ := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (coefficients b u) (coefficients b (retainedOperator A u))
  rw [(coefficients (H := H) b).inner_map_map u (retainedOperator A u)] at h
  simpa only [coefficients_retainedOperator] using h

variable (e : ι ↪ ℕ)

def countableCoefficients : TensorSpace H K →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2 :=
  (PhysicalL2HilbertSum.padding (H := H) e).comp (coefficients b).toLinearIsometry

theorem countableCoefficients_retainedOperator (A : H →L[ℂ] H)
    (u : TensorSpace H K) (n : ℕ) :
    countableCoefficients b e (retainedOperator A u) n =
      A (countableCoefficients b e u n) := by
  classical
  by_cases hn : n ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hn
    change PhysicalL2HilbertSum.padding e
      (coefficients b (retainedOperator A u))
      (e i) = A (PhysicalL2HilbertSum.padding e
      (coefficients b u) (e i))
    rw [PhysicalL2HilbertSum.padding_at, PhysicalL2HilbertSum.padding_at,
      coefficients_retainedOperator]
  · change PhysicalL2HilbertSum.padding e
      (coefficients b (retainedOperator A u)) n =
      A (PhysicalL2HilbertSum.padding e
      (coefficients b u) n)
    rw [PhysicalL2HilbertSum.padding_off _ _ n hn,
      PhysicalL2HilbertSum.padding_off _ _ n hn, map_zero]

/-- A pure tensor has retained coordinates in every submodule containing its retained factor. -/
theorem countableCoefficients_tensor_mem (V : Submodule ℂ H) (v : H) (hv : v ∈ V)
    (w : K) (n : ℕ) :
    countableCoefficients b e (tensor v w) n ∈ V := by
  classical
  by_cases hn : n ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hn
    change PhysicalL2HilbertSum.padding e
      (coefficients b (tensor v w))
      (e i) ∈ V
    rw [PhysicalL2HilbertSum.padding_at, coefficients_tensor]
    exact V.smul_mem _ hv
  · change PhysicalL2HilbertSum.padding e
      (coefficients b (tensor v w)) n ∈ V
    rw [PhysicalL2HilbertSum.padding_off _ _ n hn]
    exact V.zero_mem

theorem countableCoefficients_observable_hasSum (A : H →L[ℂ] H)
    (u : TensorSpace H K) :
    HasSum (fun n => ⟪countableCoefficients b e u n, A (countableCoefficients b e u n)⟫_ℂ)
      ⟪u, retainedOperator A u⟫_ℂ := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (countableCoefficients b e u)
    (countableCoefficients b e (retainedOperator A u))
  rw [(countableCoefficients b e).inner_map_map u (retainedOperator A u)] at h
  simpa only [countableCoefficients_retainedOperator] using h

end GptLean.PhysicalFock.TensorCoordinates

namespace GptLean.PhysicalFock

open UniformSpace Filter Topology
open scoped ENNReal InnerProductSpace

/-- A fixed actual Hilbert basis of the discarded physical photon space. -/
def environmentIndex : Set PhotonFock := (exists_hilbertBasis ℂ PhotonFock).choose

def environmentBasis : HilbertBasis environmentIndex ℂ PhotonFock :=
  (exists_hilbertBasis ℂ PhotonFock).choose_spec.choose

instance environmentIndex_countable : Countable environmentIndex :=
  PhysicalL2HilbertSum.basisIndex_countable environmentBasis

def environmentIndexEmbedding : environmentIndex ↪ ℕ := Repair.countableIndexEmbedding _

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual countable environmental coefficients, padded by zero if necessary. -/
def environmentalCoordinates :
    TensorCoordinates.TensorSpace H PhotonFock →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2 :=
  TensorCoordinates.countableCoefficients environmentBasis environmentIndexEmbedding

variable {H}

theorem environmentalCoordinates_retainedOperator (A : H →L[ℂ] H)
    (u : TensorCoordinates.TensorSpace H PhotonFock) (n : ℕ) :
    environmentalCoordinates H (TensorCoordinates.retainedOperator A u) n =
      A (environmentalCoordinates H u n) :=
  TensorCoordinates.countableCoefficients_retainedOperator environmentBasis environmentIndexEmbedding A u n

theorem environmentalCoordinates_tensor_mem (V : Submodule ℂ H) (v : H) (hv : v ∈ V)
    (w : PhotonFock) (n : ℕ) :
    environmentalCoordinates H (TensorCoordinates.tensor v w) n ∈ V :=
  TensorCoordinates.countableCoefficients_tensor_mem environmentBasis environmentIndexEmbedding V v hv w n

theorem environmentalCoordinates_observable_hasSum (A : H →L[ℂ] H)
    (u : TensorCoordinates.TensorSpace H PhotonFock) :
    HasSum (fun n => ⟪environmentalCoordinates H u n, A (environmentalCoordinates H u n)⟫_ℂ)
      ⟪u, TensorCoordinates.retainedOperator A u⟫_ℂ :=
  TensorCoordinates.countableCoefficients_observable_hasSum environmentBasis environmentIndexEmbedding A u

end GptLean.PhysicalFock
