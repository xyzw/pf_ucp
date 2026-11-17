import GptLean.PhysicalGaussianSource
import GptLean.PhysicalH1Fiber

/-!
Electronic weak derivatives pass through a fixed photon Gaussian unitary.
Finite photon coefficients preserve the weak graph. Their full L² sums
converge, and closedness of the electronic weak graph gives the almost
everywhere Gaussian-fiber conclusion.
-/

noncomputable section
namespace GptLean.PhysicalGaussianCoordinates

open MeasureTheory Filter Topology PhysicalL2HilbertSum PhysicalL2FiberSum
  ElectronicH1Complex
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section Tuple
variable {Q E I : Type*} [MeasurableSpace Q] (μ : Measure Q)
  [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Package finitely many L² classes into the actual product-valued class. -/
def tupleLp : (Lp E 2 μ × (I → Lp E 2 μ)) →L[ℂ] Lp (E × (I → E)) 2 μ :=
  ((ContinuousLinearMap.inl ℂ E (I → E)).compLpL 2 μ).comp
    (ContinuousLinearMap.fst ℂ _ _) +
  ∑ i : I, (((ContinuousLinearMap.inr ℂ E (I → E)).comp
    (ContinuousLinearMap.single ℂ (fun _ : I => E) i)).compLpL 2 μ).comp
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ _ _))

theorem tupleLp_ae (z : Lp E 2 μ × (I → Lp E 2 μ)) :
    tupleLp μ z =ᵐ[μ] fun q => (z.1 q, fun i => z.2 i q) := by
  let L := ContinuousLinearMap.inl ℂ E (I → E)
  let A (i : I) := (ContinuousLinearMap.inr ℂ E (I → E)).comp
    (ContinuousLinearMap.single ℂ (fun _ : I => E) i)
  simp only [tupleLp, add_apply, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply]
  change L.compLpL 2 μ z.1 + ∑ i, (A i).compLpL 2 μ (z.2 i) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_add (L.compLpL 2 μ z.1) (∑ i, (A i).compLpL 2 μ (z.2 i)),
    Lp.coeFn_finsetSum Finset.univ (fun i => (A i).compLpL 2 μ (z.2 i)),
    L.coeFn_compLpL z.1, ae_all_iff.mpr (fun i => (A i).coeFn_compLpL (z.2 i))]
    with q hsum hfin hL hA
  rw [hsum, Pi.add_apply, hfin, Finset.sum_apply, hL]
  simp only [hA, A, L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.single_apply]
  ext i <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.univ_sum_single]

/-- Closed relations remain closed after pointwise L² lifting. -/
theorem closed_ae_relation {Y : Type*} [NormedAddCommGroup Y]
    (s : Set Y) (hs : IsClosed s) : IsClosed {u : Lp Y 2 μ | ∀ᵐ q ∂μ, u q ∈ s} := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu huv
  obtain ⟨ns, _, hae⟩ := (tendstoInMeasure_of_tendsto_Lp huv).exists_seq_tendsto_ae
  filter_upwards [hae, ae_all_iff.mpr hu] with q hq hmem
  exact hs.mem_of_tendsto hq (Eventually.of_forall fun n => hmem (ns n))
end Tuple

section Spatial
variable {Q H K I ι : Type*} [MeasurableSpace Q] (μ : Measure Q)
  [SFinite μ] [IsSeparable μ] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]
  (U : H ≃ₗᵢ[ℂ] Lp K 2 μ)

private def scalarTensorH1 (v : H) : ComplexH1 ℂ I →L[ℂ] ComplexH1 H I :=
  ElectronicH1Map.map ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).flip v)

omit [DecidableEq I] [CompleteSpace H] in
private theorem productSource_tensor (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ I)))
    (v : H) : productSource volume μ U (tensor f v) =ᵐ[μ.prod volume]
      fun qx => f qx.2 • U v qx.1 := by
  apply ae_eq_of_swapped_sections volume μ (Lp.stronglyMeasurable _)
    (((Lp.stronglyMeasurable f).comp_measurable measurable_snd).smul
      ((Lp.stronglyMeasurable (U v)).comp_measurable measurable_fst))
  filter_upwards [productSource_represents volume μ U (tensor f v), tensor_ae f v]
    with x hx ht
  have he : U (tensor f v x) = f x • U v := by rw [ht, map_smul]
  filter_upwards [hx, Lp.coeFn_smul (f x) (U v)] with q hq hs
  rw [hq, he, hs]
  rfl

omit [DecidableEq I] [CompleteSpace H] in
theorem spatialUnitary_tensor_ae
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ I))) (v : H) :
    spatialUnitary volume μ U (tensor f v) =ᵐ[μ]
      fun q => tensor f (U v q) := by
  have hs : ∀ᵐ q ∂μ, (fun x => productSource volume μ U (tensor f v) (q, x)) =ᵐ[volume]
      fun x => f x • U v q :=
    Measure.ae_ae_of_ae_prod (productSource_tensor μ U f v)
  filter_upwards [PhysicalSourceFubini.curryEquiv_represents_ae
      (productSource volume μ U (tensor f v)), hs] with q hq ht
  apply Lp.ext
  filter_upwards [hq, ht, tensor_ae f (U v q)] with x hqx htx hvx
  exact hqx.trans (htx.trans hvx.symm)

omit [CompleteSpace H] in
private theorem tensor_weak_graph (g : ComplexH1 ℂ I) (v : H) :
    ∀ᵐ q ∂μ, (spatialUnitary volume μ U (tensor (value g) v) q,
      fun i => spatialUnitary volume μ U (tensor (derivative i g) v) q) ∈
        complexWeakGraph K I := by
  filter_upwards [spatialUnitary_tensor_ae μ U (value g) v,
    ae_all_iff.mpr (fun i => spatialUnitary_tensor_ae μ U (derivative i g) v)]
    with q hq hd
  simp only [hq, hd]
  exact (scalarTensorH1 (U v q) g).property

omit [TopologicalSpace.SeparableSpace K] in
private theorem complexWeakGraph_iff
    (z : ElectronicH1Space.L2 K I × (I → ElectronicH1Space.L2 K I)) :
    z ∈ complexWeakGraph K I ↔ SymmetricLift.HasWeakH1Local z.1 (fun i => z.2 i) := Iff.rfl

attribute [local irreducible] spatialUnitary tupleLp complexWeakGraph

set_option maxHeartbeats 800000 in
/-- Weak H¹ regularity of the actual Gaussian fibers. -/
theorem spatialUnitary_weak_graph (b : HilbertBasis ι ℂ H) (u : ComplexH1 H I) :
    ∀ᵐ q ∂μ, (spatialUnitary volume μ U (value u) q,
      fun i => spatialUnitary volume μ U (derivative i u) q) ∈ complexWeakGraph K I := by
  classical
  let V :=
    (spatialUnitary (volume : Measure (EuclideanSpace ℝ I)) μ U).toContinuousLinearEquiv.toContinuousLinearMap
  let L : (ElectronicH1Space.L2 H I × (I → ElectronicH1Space.L2 H I)) →L[ℂ]
      Lp (ElectronicH1Space.L2 K I × (I → ElectronicH1Space.L2 K I)) 2 μ :=
    (tupleLp μ).comp ((V.comp (ContinuousLinearMap.fst ℂ _ _)).prod
      (ContinuousLinearMap.pi fun i => V.comp
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ _ _))))
  let g (a : ι) := PhysicalH1Fiber.coefficient b a u
  let t (a : ι) : ElectronicH1Space.L2 H I × (I → ElectronicH1Space.L2 H I) :=
    (tensor (value (g a)) (b a), fun i => tensor (derivative i (g a)) (b a))
  let z (s : Finset ι) : ElectronicH1Space.L2 H I × (I → ElectronicH1Space.L2 H I) :=
    ∑ a ∈ s, t a
  have hv : Tendsto (fun s => (z s).1) atTop (𝓝 (value u)) := by
    simpa only [z, t, Prod.fst_sum, g, PhysicalH1Fiber.value_coefficient, HasSum,
      SummationFilter.unconditional_filter] using hasSum_tensor_fiberCoefficients b (value u)
  have hd : Tendsto (fun s => (z s).2) atTop (𝓝 (fun i => derivative i u)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [z, t, Prod.snd_sum, Finset.sum_apply, g,
      PhysicalH1Fiber.derivative_coefficient, HasSum,
      SummationFilter.unconditional_filter] using hasSum_tensor_fiberCoefficients b (derivative i u)
  have hL (y : ElectronicH1Space.L2 H I × (I → ElectronicH1Space.L2 H I)) :
      L y = tupleLp μ (V y.1, fun i => V (y.2 i)) := by
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_pi', ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply]
  have ht (a : ι) : ∀ᵐ q ∂μ, L (t a) q ∈ complexWeakGraph K I := by
    rw [hL]
    filter_upwards [tupleLp_ae μ
      (V (t a).1, fun i => V ((t a).2 i)),
      tensor_weak_graph μ U (g a) (b a)] with q hq hmem
    rw [hq]
    exact hmem
  have hm (s : Finset ι) : ∀ᵐ q ∂μ, L (z s) q ∈ complexWeakGraph K I := by
    have hsum : L (z s) = ∑ a ∈ s, L (t a) := map_sum L t s
    rw [hsum]
    filter_upwards [Lp.coeFn_finsetSum s (fun a => L (t a)),
      (Filter.eventually_all_finset s).mpr (fun a _ => ht a)] with q hq hmem
    rw [hq, Finset.sum_apply]
    exact (complexWeakGraph K I).sum_mem (fun a ha => hmem a ha)
  have hclosed : IsClosed {w : Lp (ElectronicH1Space.L2 K I ×
      (I → ElectronicH1Space.L2 K I)) 2 μ |
      ∀ᵐ q ∂μ, w q ∈ complexWeakGraph K I} :=
    closed_ae_relation (Y := ElectronicH1Space.L2 K I ×
      (I → ElectronicH1Space.L2 K I)) μ
      (complexWeakGraph K I : Set (ElectronicH1Space.L2 K I ×
        (I → ElectronicH1Space.L2 K I)))
      (isClosed_complexWeakGraph (E := K) (I := I))
  have hlim := L.continuous.tendsto (value u, fun i => derivative i u) |>.comp (hv.prodMk_nhds hd)
  have h := hclosed.mem_of_tendsto hlim (Eventually.of_forall hm)
  rw [hL] at h
  filter_upwards [h, tupleLp_ae μ
    (V (value u), fun i => V (derivative i u))] with q hq he
  exact he ▸ hq

/-- The original product-source representatives have the same derivatives. -/
theorem productSource_weak (b : HilbertBasis ι ℂ H) (u : ComplexH1 H I) :
    ∀ᵐ q ∂μ, SymmetricLift.HasWeakH1Local
      (fun x => productSource volume μ U (value u) (q, x))
      (fun i x => productSource volume μ U (derivative i u) (q, x)) := by
  filter_upwards [spatialUnitary_weak_graph μ U b u,
    PhysicalSourceFubini.curryEquiv_represents_ae (productSource volume μ U (value u)),
    ae_all_iff.mpr (fun i => PhysicalSourceFubini.curryEquiv_represents_ae
      (productSource volume μ U (derivative i u)))] with q hq hv hd
  simp only [spatialUnitary_source] at hq
  exact ((complexWeakGraph_iff _).mp hq).congr hv (fun i => hd i)
end Spatial
end GptLean.PhysicalGaussianCoordinates
