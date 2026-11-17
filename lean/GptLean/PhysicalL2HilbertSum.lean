import GptLean.PhysicalSourceFubiniEquiv
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Expanding the scalar spatial factor in a Hilbert basis gives an actual
unitary from Hilbert-valued L² to a Hilbert sum of its fiber. Simple-function
density proves completeness of the expansion. Every bounded fiber operator
acts coordinatewise under this unitary.
-/

noncomputable section
namespace GptLean.PhysicalL2HilbertSum

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {X H ι : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar L² multiplication by a constant fiber vector, as a bilinear map. -/
def tensor : Lp ℂ 2 μ →L[ℂ] H →L[ℂ] Lp H 2 μ :=
  ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).flip.compLpL₂ 2 μ).flip

omit [CompleteSpace H] in
theorem tensor_ae (f : Lp ℂ 2 μ) (v : H) :
    tensor f v =ᵐ[μ] fun x => f x • v :=
  ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).flip v).coeFn_compLp f

omit [CompleteSpace H] in
theorem tensor_inner (f g : Lp ℂ 2 μ) (v w : H) :
    ⟪tensor f v, tensor g w⟫_ℂ = ⟪f, g⟫_ℂ * ⟪v, w⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [tensor_ae f v, tensor_ae g w] with x hx hy
  rw [hx, hy]
  simp only [inner_smul_left, inner_smul_right, RCLike.inner_apply]
  ring

variable (b : HilbertBasis ι ℂ (Lp ℂ 2 μ))

def insertion (i : ι) : H →ₗᵢ[ℂ] Lp H 2 μ :=
  (tensor (b i)).toLinearMap.isometryOfInner (fun v w => by
    change ⟪tensor (b i) v, tensor (b i) w⟫_ℂ = _
    rw [tensor_inner, inner_self_eq_one_of_norm_eq_one (b.orthonormal.norm_eq_one i), one_mul])

omit [CompleteSpace H] in
@[simp] theorem insertion_apply (i : ι) (v : H) : insertion (H := H) b i v = tensor (b i) v := rfl

omit [CompleteSpace H] in
theorem insertion_orthogonal : OrthogonalFamily ℂ (fun _ : ι => H) (insertion b) := by
  intro i j hij v w
  rw [insertion_apply, insertion_apply, tensor_inner, b.orthonormal.2 hij, zero_mul]

omit [CompleteSpace H] in
private theorem tensor_mem_spanClosure (f : Lp ℂ 2 μ) (v : H) :
    tensor f v ∈ (⨆ i, LinearMap.range (insertion (H := H) b i).toLinearMap).topologicalClosure := by
  have hs := (tensor.flip v).hasSum (b.hasSum_repr f)
  change tensor.flip v f ∈ closure ((⨆ i, LinearMap.range (insertion (H := H) b i).toLinearMap : Submodule ℂ (Lp H 2 μ)) : Set (Lp H 2 μ))
  apply mem_closure_of_tendsto hs
  apply Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  exact Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self (insertion (H := H) b i).toLinearMap v)

omit [CompleteSpace H] in
private theorem tensor_indicator {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (v : H) :
    tensor (indicatorConstLp 2 hs hμs (1 : ℂ)) v = indicatorConstLp 2 hs hμs v := by
  apply Lp.ext
  filter_upwards [tensor_ae (indicatorConstLp 2 hs hμs (1 : ℂ)) v,
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := hμs) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := hμs) (c := v)]
    with x ht hf hv
  rw [ht, hf, hv]
  by_cases hx : x ∈ s <;> simp [hx]

omit [CompleteSpace H] in
/-- The scalar spatial basis spans all Hilbert-valued L², by simple-function density. -/
theorem insertion_total :
    ⊤ ≤ (⨆ i, LinearMap.range (insertion (H := H) b i).toLinearMap).topologicalClosure := by
  intro u _
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (fun u => u ∈ (⨆ i, LinearMap.range (insertion (H := H) b i).toLinearMap).topologicalClosure)
  · intro v s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, ← tensor_indicator hs hμs.ne v]
    exact tensor_mem_spanClosure b _ v
  · intro f g hf hg _ hfm hgm
    exact Submodule.add_mem _ hfm hgm
  · exact Submodule.isClosed_topologicalClosure _

theorem hilbertSum : IsHilbertSum ℂ (fun _ : ι => H) (insertion b) :=
  IsHilbertSum.mk (insertion_orthogonal b) (insertion_total (H := H) b)

/-- The spatial coefficient unitary on the same L² classes. -/
def coefficients : Lp H 2 μ ≃ₗᵢ[ℂ] lp (fun _ : ι => H) 2 :=
  (hilbertSum b).linearIsometryEquiv

theorem coefficients_inner (u : Lp H 2 μ) (i : ι) (v : H) :
    ⟪v, coefficients b u i⟫_ℂ = ⟪tensor (b i) v, u⟫_ℂ := by
  classical
  rw [← lp.inner_single_left i v (coefficients b u),
    ← (coefficients b).symm.inner_map_map (lp.single 2 i v) (coefficients b u),
    LinearIsometryEquiv.symm_apply_apply]
  change ⟪(hilbertSum b).linearIsometryEquiv.symm (lp.single 2 i v), u⟫_ℂ = _
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply_single, insertion_apply]

private theorem tensor_inner_compLpL (f : Lp ℂ 2 μ) (v : H) (B : H →L[ℂ] H) (u : Lp H 2 μ) :
    ⟪tensor f v, B.compLpL 2 μ u⟫_ℂ = ⟪tensor f (B.adjoint v), u⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensor_ae f v, tensor_ae f (B.adjoint v), B.coeFn_compLpL u] with x hv hw hB
  rw [hv, hw, hB, inner_smul_left, inner_smul_left, B.adjoint_inner_left]

/-- Every bounded fiber operator is diagonal in the actual spatial expansion. -/
theorem coefficients_compLpL (B : H →L[ℂ] H) (u : Lp H 2 μ) (i : ι) :
    coefficients b (B.compLpL 2 μ u) i = B (coefficients b u i) := by
  apply ext_inner_left ℂ
  intro v
  rw [coefficients_inner, tensor_inner_compLpL, ← coefficients_inner, B.adjoint_inner_left]

theorem coefficients_observable_hasSum (B : H →L[ℂ] H) (u : Lp H 2 μ) :
    HasSum (fun i => ⟪coefficients b u i, B (coefficients b u i)⟫_ℂ)
      ⟪u, B.compLpL 2 μ u⟫_ℂ := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (coefficients b u) (coefficients b (B.compLpL 2 μ u))
  rw [(coefficients (H := H) b).inner_map_map u (B.compLpL 2 μ u)] at h
  simpa only [coefficients_compLpL] using h

end GptLean.PhysicalL2HilbertSum
