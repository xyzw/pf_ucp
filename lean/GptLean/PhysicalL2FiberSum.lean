import GptLean.PhysicalL2HilbertSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
An actual fiber-basis expansion of Hilbert-valued L2. Scalar spatial
operators lift through this unitary, commute with every bounded fiber
operator, and preserve positivity. The construction uses simple-function
density and Parseval and assumes no tensor compatibility identities.
-/

noncomputable section

namespace GptLean.PhysicalL2FiberSum

open MeasureTheory Filter Topology PhysicalL2HilbertSum
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {X H ι : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (b : HilbertBasis ι ℂ H)

def insertion (i : ι) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp H 2 μ :=
  (tensor.flip (b i)).toLinearMap.isometryOfInner (fun f g => by
    change ⟪tensor f (b i), tensor g (b i)⟫_ℂ = _
    rw [tensor_inner, inner_self_eq_one_of_norm_eq_one (b.orthonormal.norm_eq_one i), mul_one])

omit [CompleteSpace H] in
@[simp] theorem insertion_apply (i : ι) (f : Lp ℂ 2 μ) :
    insertion b i f = tensor f (b i) := rfl

omit [CompleteSpace H] in
theorem insertion_orthogonal :
    OrthogonalFamily ℂ (fun _ : ι => Lp ℂ 2 μ) (insertion (μ := μ) b) := by
  intro i j hij f g
  rw [insertion_apply, insertion_apply, tensor_inner, b.orthonormal.2 hij, mul_zero]

omit [CompleteSpace H] in
private theorem tensor_mem_spanClosure (f : Lp ℂ 2 μ) (v : H) :
    tensor f v ∈ (⨆ i, LinearMap.range (insertion (μ := μ) b i).toLinearMap).topologicalClosure := by
  have hs := (tensor f).hasSum (b.hasSum_repr v)
  change tensor f v ∈ closure ((⨆ i, LinearMap.range
    (insertion (μ := μ) b i).toLinearMap : Submodule ℂ (Lp H 2 μ)) : Set (Lp H 2 μ))
  apply mem_closure_of_tendsto hs
  apply Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  exact Submodule.mem_iSup_of_mem i
    (LinearMap.mem_range_self (insertion (μ := μ) b i).toLinearMap f)

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
theorem insertion_total :
    ⊤ ≤ (⨆ i, LinearMap.range (insertion (μ := μ) b i).toLinearMap).topologicalClosure := by
  intro u _
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (fun u => u ∈ (⨆ i, LinearMap.range
      (insertion (μ := μ) b i).toLinearMap).topologicalClosure)
  · intro v s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, ← tensor_indicator hs hμs.ne v]
    exact tensor_mem_spanClosure b _ v
  · intro f g hf hg _ hfm hgm
    exact Submodule.add_mem _ hfm hgm
  · exact Submodule.isClosed_topologicalClosure _

def fiberCoefficients : Lp H 2 μ ≃ₗᵢ[ℂ] lp (fun _ : ι => Lp ℂ 2 μ) 2 :=
  (IsHilbertSum.mk (insertion_orthogonal (μ := μ) b)
    (insertion_total (μ := μ) b)).linearIsometryEquiv

theorem fiberCoefficients_inner (u : Lp H 2 μ) (i : ι) (f : Lp ℂ 2 μ) :
    ⟪f, fiberCoefficients b u i⟫_ℂ = ⟪tensor f (b i), u⟫_ℂ := by
  classical
  rw [← lp.inner_single_left i f (fiberCoefficients b u),
    ← (fiberCoefficients b).symm.inner_map_map (lp.single 2 i f) (fiberCoefficients b u),
    LinearIsometryEquiv.symm_apply_apply]
  change ⟪(IsHilbertSum.mk (insertion_orthogonal b) (insertion_total b)).linearIsometryEquiv.symm
    (lp.single 2 i f), u⟫_ℂ = _
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply_single, insertion_apply]

theorem fiberCoefficients_symm_single [DecidableEq ι] (i : ι) (f : Lp ℂ 2 μ) :
    (fiberCoefficients b).symm (lp.single 2 i f) = tensor f (b i) := by
  classical
  change (IsHilbertSum.mk (insertion_orthogonal b) (insertion_total b)).linearIsometryEquiv.symm
    (lp.single 2 i f) = _
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply_single, insertion_apply]

theorem hasSum_tensor_fiberCoefficients (u : Lp H 2 μ) :
    HasSum (fun i => tensor (fiberCoefficients b u i) (b i)) u := by
  classical
  have hs : HasSum (fun i => (fiberCoefficients b).symm
      (lp.single 2 i (fiberCoefficients b u i)))
      ((fiberCoefficients b).symm (fiberCoefficients b u)) :=
    (fiberCoefficients b).symm.toLinearIsometry.toContinuousLinearMap.hasSum
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (fiberCoefficients b u))
  simpa only [fiberCoefficients_symm_single, LinearIsometryEquiv.symm_apply_apply] using hs

theorem fiberCoefficients_apply (u : Lp H 2 μ) (i : ι) :
    fiberCoefficients b u i = (innerSL ℂ (b i)).compLpL 2 μ u := by
  apply ext_inner_left ℂ
  intro f
  rw [fiberCoefficients_inner, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensor_ae f (b i), (innerSL ℂ (b i)).coeFn_compLpL u]
    with x hf hu
  rw [hf, hu, inner_smul_left]
  simp only [RCLike.inner_apply', innerSL_apply_apply]

theorem fiberCoefficients_tensor (f : Lp ℂ 2 μ) (v : H) (i : ι) :
    fiberCoefficients b (tensor f v) i = ⟪b i, v⟫_ℂ • f := by
  apply ext_inner_left ℂ
  intro g
  rw [fiberCoefficients_inner, tensor_inner, inner_smul_right]
  ring

private def coordinateOperator (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    lp (fun _ : ι => Lp ℂ 2 μ) 2 →L[ℂ] lp (fun _ : ι => Lp ℂ 2 μ) 2 :=
  lp.mapCLM 2 (fun _ => A) (norm_nonneg A) (fun _ => le_rfl)

def liftSpatial (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  (fiberCoefficients b).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((coordinateOperator (ι := ι) A).comp
      (fiberCoefficients b).toLinearIsometry.toContinuousLinearMap)

theorem fiberCoefficients_liftSpatial (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (u : Lp H 2 μ) (i : ι) :
    fiberCoefficients b (liftSpatial b A u) i = A (fiberCoefficients b u i) := by
  change fiberCoefficients b ((fiberCoefficients b).symm
    (coordinateOperator A (fiberCoefficients b u))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem liftSpatial_norm_le (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : ‖liftSpatial b A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro u
  calc
    ‖liftSpatial b A u‖ = ‖coordinateOperator (ι := ι) A (fiberCoefficients b u)‖ :=
      (fiberCoefficients b).symm.norm_map _
    _ ≤ ‖A‖ * ‖fiberCoefficients b u‖ :=
      (coordinateOperator (ι := ι) A).le_of_opNorm_le
        (lp.norm_mapCLM_le 2 (fun _ : ι => A) (norm_nonneg A) (fun _ => le_rfl)) _
    _ = ‖A‖ * ‖u‖ := by rw [(fiberCoefficients b).norm_map]

theorem liftSpatial_tensor (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (f : Lp ℂ 2 μ) (v : H) :
    liftSpatial b A (tensor f v) = tensor (A f) v := by
  apply (fiberCoefficients b).injective
  apply lp.ext
  funext i
  rw [fiberCoefficients_liftSpatial, fiberCoefficients_tensor, fiberCoefficients_tensor, map_smul]

omit [CompleteSpace H] in
private theorem compLpL_tensor (B : H →L[ℂ] H) (f : Lp ℂ 2 μ) (v : H) :
    B.compLpL 2 μ (tensor f v) = tensor f (B v) := by
  apply Lp.ext
  filter_upwards [B.coeFn_compLpL (tensor f v), tensor_ae f v, tensor_ae f (B v)]
    with x hB hv hw
  rw [hB, hv, hw, map_smul]

theorem liftSpatial_compLpL (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (B : H →L[ℂ] H) :
    (liftSpatial b A).comp (B.compLpL 2 μ) = (B.compLpL 2 μ).comp (liftSpatial b A) := by
  apply ContinuousLinearMap.ext
  intro u
  change liftSpatial b A (B.compLpL 2 μ u) = B.compLpL 2 μ (liftSpatial b A u)
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (fun u => liftSpatial b A (B.compLpL 2 μ u) = B.compLpL 2 μ (liftSpatial b A u))
  · intro v s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, ← tensor_indicator hs hμs.ne v,
      compLpL_tensor, liftSpatial_tensor, liftSpatial_tensor, compLpL_tensor]
  · intro f g hf hg _ hfm hgm
    simp only [map_add, hfm, hgm]
  · exact isClosed_eq ((liftSpatial b A).continuous.comp (B.compLpL 2 μ).continuous)
      ((B.compLpL 2 μ).continuous.comp (liftSpatial b A).continuous)

theorem liftSpatial_quadratic_hasSum (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (u : Lp H 2 μ) :
    HasSum (fun i => ⟪fiberCoefficients b u i, A (fiberCoefficients b u i)⟫_ℂ)
      ⟪u, liftSpatial b A u⟫_ℂ := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (fiberCoefficients b u)
    (fiberCoefficients b (liftSpatial b A u))
  rw [(fiberCoefficients b).inner_map_map] at h
  simpa only [fiberCoefficients_liftSpatial] using h

set_option backward.isDefEq.respectTransparency.types true in
theorem liftSpatial_isSymmetric (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hA : A.IsSymmetric) :
    (liftSpatial b A).IsSymmetric := by
  intro u v
  have h₁ := (lp.hasSum_inner (𝕜 := ℂ)
    (fiberCoefficients b (liftSpatial b A u)) (fiberCoefficients b v)).congr_fun
      (fun i => congrArg (fun z => inner ℂ z (fiberCoefficients b v i))
        (fiberCoefficients_liftSpatial b A u i).symm)
  have h₂ := (lp.hasSum_inner (𝕜 := ℂ)
    (fiberCoefficients b u) (fiberCoefficients b (liftSpatial b A v))).congr_fun
      (fun i => (hA (fiberCoefficients b u i) (fiberCoefficients b v i)).trans
        (congrArg (fun z => inner ℂ (fiberCoefficients b u i) z)
          (fiberCoefficients_liftSpatial b A v i).symm))
  rw [(fiberCoefficients b).inner_map_map] at h₁ h₂
  exact h₁.unique h₂

theorem liftSpatial_real_quadratic_hasSum (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (u : Lp H 2 μ) :
    HasSum (fun i => (inner ℂ (fiberCoefficients b u i) (A (fiberCoefficients b u i))).re)
      (inner ℂ u (liftSpatial b A u)).re :=
  Complex.reCLM.hasSum (liftSpatial_quadratic_hasSum b A u)

theorem liftSpatial_quadratic_nonneg (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hA : ∀ f, 0 ≤ (inner ℂ f (A f)).re) (u : Lp H 2 μ) :
    0 ≤ (inner ℂ u (liftSpatial b A u)).re := by
  have hs := liftSpatial_real_quadratic_hasSum b A u
  calc
    0 ≤ ∑' i, (inner ℂ (fiberCoefficients b u i) (A (fiberCoefficients b u i))).re :=
      tsum_nonneg (fun i => hA (fiberCoefficients b u i))
    _ = _ := hs.tsum_eq

theorem liftSpatial_isPositive (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hA : A.IsPositive) :
    (liftSpatial b A).IsPositive := by
  refine ⟨liftSpatial_isSymmetric b A hA.isSymmetric, ?_⟩
  intro u
  change 0 ≤ (inner ℂ (liftSpatial b A u) u).re
  exact (liftSpatial_quadratic_nonneg b A hA.re_inner_nonneg_right u).trans_eq
    (inner_re_symm (𝕜 := ℂ) u (liftSpatial b A u))

theorem liftSpatial_quadratic_le (A D : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hAD : ∀ f, (inner ℂ f (A f)).re ≤ (inner ℂ f (D f)).re) (u : Lp H 2 μ) :
    (inner ℂ u (liftSpatial b A u)).re ≤ (inner ℂ u (liftSpatial b D u)).re := by
  have hA := liftSpatial_real_quadratic_hasSum b A u
  have hD := liftSpatial_real_quadratic_hasSum b D u
  exact hasSum_le (fun i => hAD (fiberCoefficients b u i)) hA hD

end GptLean.PhysicalL2FiberSum
