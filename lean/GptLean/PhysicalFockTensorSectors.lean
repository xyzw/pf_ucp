import GptLean.PhysicalFockExponential
import GptLean.PhysicalFockFiniteOperators

/-!
Actual pairs of photon-number sectors in the completed two-Fock tensor.

The pair insertions are tensor products of the canonical lp insertions.
Their orthogonality and completeness construct a unitary sector expansion.
The matched exponential map sends source number n into pairs whose two
photon numbers sum to n.
-/

noncomputable section
namespace GptLean.PhysicalFock.TensorSectors

open UniformSpace Filter Topology MeasureTheory
open scoped ENNReal InnerProductSpace
open TensorCoordinates

set_option backward.isDefEq.respectTransparency.types false

variable (K : ℕ → Type*) [∀ n, NormedAddCommGroup (K n)]
  [∀ n, InnerProductSpace ℂ (K n)]

def singleIsometry (n : ℕ) : K n →ₗᵢ[ℂ] Space K where
  toLinearMap := (lp.singleContinuousLinearMap ℂ K 2 n).toLinearMap
  norm_map' u := lp.norm_single (E := K) (p := 2) (by norm_num) n u

def pairInsertion (p : ℕ × ℕ) :
    TensorSpace (K p.1) (K p.2) →ₗᵢ[ℂ] TensorSpace (Space K) (Space K) :=
  (TensorProduct.mapIsometry (singleIsometry K p.1) (singleIsometry K p.2)).completion

theorem pairInsertion_tensor (p : ℕ × ℕ) (u : K p.1) (v : K p.2) :
    pairInsertion K p (tensor u v) = tensor (lp.single 2 p.1 u) (lp.single 2 p.2 v) := by
  rw [tensor_apply, pairInsertion, LinearIsometry.completion_apply_coe]
  rfl

private theorem inner_zero_of_tensors
    {A B C D H : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : TensorSpace A B →L[ℂ] H) (V : TensorSpace C D →L[ℂ] H)
    (h : ∀ a b c d, ⟪U (tensor a b), V (tensor c d)⟫_ℂ = 0)
    (u : TensorSpace A B) (v : TensorSpace C D) : ⟪U u, V v⟫_ℂ = 0 := by
  have hpure (a : A) (b : B) : ∀ v : TensorSpace C D, ⟪U (tensor a b), V v⟫_ℂ = 0 := by
    intro v
    induction v using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) continuous_const
    | ih v =>
      induction v using TensorProduct.induction_on with
      | zero => simp only [Completion.coe_zero, map_zero, inner_zero_right]
      | tmul c d => exact h a b c d
      | add v w hv hw =>
        simp only [Completion.coe_add, map_add, inner_add_right, hv, hw, add_zero]
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_const
  | ih u =>
    induction u using TensorProduct.induction_on with
    | zero => simp only [Completion.coe_zero, map_zero, inner_zero_left]
    | tmul a b => exact hpure a b v
    | add u w hu hw =>
      simp only [Completion.coe_add, map_add, inner_add_left, hu, hw, add_zero]

theorem pairInsertion_orthogonal :
    OrthogonalFamily ℂ (fun p : ℕ × ℕ => TensorSpace (K p.1) (K p.2)) (pairInsertion K) := by
  intro p q hpq u v
  apply inner_zero_of_tensors (pairInsertion K p).toContinuousLinearMap
    (pairInsertion K q).toContinuousLinearMap _ u v
  intro a b c d
  change ⟪pairInsertion K p (tensor a b), pairInsertion K q (tensor c d)⟫_ℂ = 0
  rw [pairInsertion_tensor, pairInsertion_tensor, tensor_inner,
    lp.inner_single_left, lp.inner_single_left]
  by_cases h : p.1 = q.1
  · have h' : p.2 ≠ q.2 := fun hs => hpq (Prod.ext h hs)
    rw [lp.single_apply_ne _ _ _ h', inner_zero_right, mul_zero]
  · rw [lp.single_apply_ne _ _ _ h, inner_zero_right, zero_mul]

private theorem tensor_mem_pair_span (v w : Space K) :
    tensor v w ∈ (⨆ p : ℕ × ℕ,
      LinearMap.range (pairInsertion K p).toLinearMap).topologicalClosure := by
  let M := (⨆ p : ℕ × ℕ, LinearMap.range (pairInsertion K p).toLinearMap).topologicalClosure
  have hfirst (s : ℕ) (b : K s) : tensor v (lp.single 2 s b) ∈ M := by
    have hs := (tensor.flip (lp.single 2 s b)).hasSum (sector_hasSum K v)
    apply mem_closure_of_tendsto hs
    apply Eventually.of_forall
    intro t
    apply Submodule.sum_mem
    intro r _
    change tensor (lp.single 2 r (v r)) (lp.single 2 s b) ∈ _
    rw [← pairInsertion_tensor K (r, s)]
    exact Submodule.mem_iSup_of_mem (r, s)
      (LinearMap.mem_range_self (pairInsertion K (r, s)).toLinearMap (tensor (v r) b))
  have hs := (tensor v).hasSum (sector_hasSum K w)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hs
  apply Eventually.of_forall
  intro t
  apply Submodule.sum_mem
  intro s _
  exact hfirst s (w s)

theorem pairInsertion_total :
    ⊤ ≤ (⨆ p : ℕ × ℕ, LinearMap.range (pairInsertion K p).toLinearMap).topologicalClosure := by
  intro u hu
  clear hu
  induction u using Completion.induction_on with
  | hp => exact Submodule.isClosed_topologicalClosure _
  | ih u =>
    induction u using TensorProduct.induction_on with
    | zero => rw [Completion.coe_zero]; exact Submodule.zero_mem _
    | tmul v w => exact tensor_mem_pair_span K v w
    | add u v hu hv => simpa only [Completion.coe_add] using Submodule.add_mem _ hu hv

def pairCoefficients : TensorSpace (Space K) (Space K) ≃ₗᵢ[ℂ]
    lp (fun p : ℕ × ℕ => TensorSpace (K p.1) (K p.2)) 2 :=
  (IsHilbertSum.mk (pairInsertion_orthogonal K) (pairInsertion_total K)).linearIsometryEquiv

def pairCoordinate (p : ℕ × ℕ) :
    TensorSpace (Space K) (Space K) →L[ℂ] TensorSpace (K p.1) (K p.2) :=
  (lp.evalCLM ℂ (fun p : ℕ × ℕ => TensorSpace (K p.1) (K p.2)) 2 p).comp
    (pairCoefficients K).toLinearIsometry.toContinuousLinearMap

theorem pairCoordinate_apply (p : ℕ × ℕ) (u : TensorSpace (Space K) (Space K)) :
    pairCoordinate K p u = pairCoefficients K u p := rfl

theorem pairCoefficients_inner (u : TensorSpace (Space K) (Space K)) (p : ℕ × ℕ)
    (z : TensorSpace (K p.1) (K p.2)) :
    ⟪z, pairCoefficients K u p⟫_ℂ = ⟪pairInsertion K p z, u⟫_ℂ := by
  classical
  rw [← lp.inner_single_left p z (pairCoefficients K u),
    ← (pairCoefficients K).symm.inner_map_map (lp.single 2 p z) (pairCoefficients K u),
    LinearIsometryEquiv.symm_apply_apply]
  change ⟪(IsHilbertSum.mk (pairInsertion_orthogonal K) (pairInsertion_total K)).linearIsometryEquiv.symm
    (lp.single 2 p z), u⟫_ℂ = _
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply_single]

private theorem pairInsertion_inner_tensor (p : ℕ × ℕ)
    (z : TensorSpace (K p.1) (K p.2)) (v w : Space K) :
    ⟪pairInsertion K p z, tensor v w⟫_ℂ = ⟪z, tensor (v p.1) (w p.2)⟫_ℂ := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [Completion.coe_zero, map_zero, inner_zero_left]
    | tmul a b =>
      rw [← tensor_apply, pairInsertion_tensor, tensor_inner, tensor_inner,
        lp.inner_single_left, lp.inner_single_left]
    | add z z' hz hz' =>
      simp only [Completion.coe_add, map_add, inner_add_left, hz, hz']

theorem pairCoefficients_tensor (v w : Space K) (p : ℕ × ℕ) :
    pairCoefficients K (tensor v w) p = tensor (v p.1) (w p.2) := by
  apply ext_inner_left ℂ
  intro z
  rw [pairCoefficients_inner, pairInsertion_inner_tensor]

end GptLean.PhysicalFock.TensorSectors

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace
open TensorCoordinates TensorSectors

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

omit [SigmaFinite μ] in
private theorem assignment_length_sum
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) :
    ∀ p ∈ splitAssignments μ j w, p.1.length + p.2.length = w.length := by
  induction w with
  | nil => simp [splitAssignments]
  | cons g w ih =>
    intro p hp
    simp only [splitAssignments, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · simp only [List.length_cons]
      have h := ih q hq
      omega
    · simp only [List.length_cons]
      have h := ih q hq
      omega

variable (B : ConcreteExponentialLaw μ)

private theorem map_list_eq_zero {α H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A : H →L[ℂ] K) (l : List α) (f : α → H)
    (h : ∀ x ∈ l, A (f x) = 0) : A ((l.map f).sum) = 0 := by
  rw [map_list_sum]
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  exact h x hx

theorem split_word_pair_zero
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) (p : ℕ × ℕ) (hp : p.1 + p.2 ≠ w.length) :
    pairCoefficients (Sector μ) (B.split μ j (creationWord μ w)) p = 0 := by
  let A : TensorSpace (Fock μ) (Fock μ) →L[ℂ] TensorSpace (Sector μ p.1) (Sector μ p.2) :=
    pairCoordinate (Sector μ) p
  have hsplit : A (splitCreationTensor μ j w) = 0 := by
    apply map_list_eq_zero A (splitAssignments μ j w)
      (fun q => tensor (creationWord μ q.1) (creationWord μ q.2))
    intro q hq
    change pairCoefficients (Sector μ) (tensor (creationWord μ q.1) (creationWord μ q.2)) p = 0
    rw [pairCoefficients_tensor]
    change tensor ((lp.single 2 q.1.length (creationWordSector μ q.1)) p.1)
      ((lp.single 2 q.2.length (creationWordSector μ q.2)) p.2) = 0
    by_cases hr : p.1 = q.1.length
    · have hs : p.2 ≠ q.2.length := by
        intro hs
        apply hp
        rw [hr, hs]
        exact assignment_length_sum μ j w q hq
      rw [lp.single_apply_ne _ _ _ hs, map_zero]
    · rw [lp.single_apply_ne _ _ _ hr]
      simp only [map_zero, zero_apply]
  exact (congrArg A (B.split_word μ j w)).trans hsplit

/-- The exponential map preserves total photon number on the actual tensor sectors. -/
theorem split_sector_pair_zero
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (n : ℕ) (u : Fock μ) (p : ℕ × ℕ) (hp : p.1 + p.2 ≠ n) :
    pairCoefficients (Sector μ) (B.split μ j (photonSector μ n u)) p = 0 := by
  let A : Fock μ →L[ℂ] TensorSpace (Sector μ p.1) (Sector μ p.2) := (pairCoordinate (Sector μ) p).comp
    ((B.split μ j).toContinuousLinearMap.comp (photonSector μ n))
  have hw : ∀ w, A (creationWord μ w) =
      (0 : Fock μ →L[ℂ] TensorSpace (Sector μ p.1) (Sector μ p.2)) (creationWord μ w) := by
    intro w
    change pairCoefficients (Sector μ) (B.split μ j (photonSector μ n (creationWord μ w))) p = 0
    rw [photonSector_word]
    split_ifs with h
    · exact split_word_pair_zero μ B j w p (h ▸ hp)
    · simp only [map_zero, lp.coeFn_zero, Pi.zero_apply]
  have he : A = 0 := B.ext_words μ A 0 hw
  exact congrArg (fun L : Fock μ →L[ℂ] TensorSpace (Sector μ p.1) (Sector μ p.2) => L u) he

/-- A tensor pair coordinate depends only on its matching source total-number sector. -/
theorem split_pair_eq_sector
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (u : Fock μ) (p : ℕ × ℕ) :
    pairCoefficients (Sector μ) (B.split μ j u) p =
      pairCoefficients (Sector μ) (B.split μ j (photonSector μ (p.1 + p.2) u)) p := by
  let A := (pairCoordinate (Sector μ) p).comp (B.split μ j).toContinuousLinearMap
  have hs := A.hasSum (photonSector_hasSum μ u)
  have hterm (n : ℕ) : A (photonSector μ n u) =
      if n = p.1 + p.2 then A (photonSector μ (p.1 + p.2) u) else 0 := by
    split_ifs with h
    · exact congrArg (fun m => A (photonSector μ m u)) h
    · exact split_sector_pair_zero μ B j n u p (Ne.symm h)
  exact (hs.congr_fun (fun n => (hterm n).symm)).unique
    (hasSum_ite_eq (p.1 + p.2) (A (photonSector μ (p.1 + p.2) u)))

end GptLean.PhysicalFock
