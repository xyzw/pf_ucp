import GptLean.Gaussian.CovariantSlicing

/-! Closed graph slicing with different source and target spaces, followed
by the ordinary Fubini representative identification. This supplies the
product-space representatives from core intertwinings. -/

noncomputable section

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology

variable {Q X H H' K K' : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K']

theorem unitary_closed_graph_between_of_hasCore
    (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (V : H' ≃ₗᵢ[ℂ] Lp K' 2 μ)
    (D : H →ₗ.[ℂ] H') (hD : D.IsClosed)
    (C : Q → K →ₗ.[ℂ] K') (hC : ∀ᵐ q ∂μ, (C q).IsClosed)
    (S : Submodule ℂ H) (hS : D.HasCore S)
    (hcore : ∀ ψ : S, ∀ᵐ q ∂μ,
      (unitaryFiber U (ψ : H) q,
        unitaryFiber V (D ⟨ψ, hS.le_domain ψ.property⟩) q) ∈ (C q).graph)
    (ψ : D.domain) :
    ∀ᵐ q ∂μ, (unitaryFiber U (ψ : H) q, unitaryFiber V (D ψ) q) ∈ (C q).graph := by
  have hcl : (D.domRestrict S).IsClosable :=
    hD.isClosable.leIsClosable LinearPMap.domRestrict_le
  have hmem : ((ψ : H), D ψ) ∈ closure ((D.domRestrict S).graph : Set (H × H')) := by
    change ((ψ : H), D ψ) ∈ (D.domRestrict S).graph.topologicalClosure
    rw [hcl.graph_closure_eq_closure_graph, hS.closure_eq]
    exact D.mem_graph ψ
  obtain ⟨w, hw, hwlim⟩ := mem_closure_iff_seq_limit.mp hmem
  choose un hun hdun using fun n => (D.domRestrict S).mem_graph_iff.mp (hw n)
  let vn (n : ℕ) : D.domain := ⟨un n, (un n).property.2⟩
  have hvn (n : ℕ) : (vn n : H) = (w n).1 := hun n
  have hdvn (n : ℕ) : D (vn n) = (w n).2 := hdun n
  have hv : Tendsto (fun n => (vn n : H)) atTop (𝓝 (ψ : H)) := by
    simpa only [hvn, Function.comp_def] using
      (continuous_fst.tendsto ((ψ : H), D ψ)).comp hwlim
  have hdv : Tendsto (fun n => D (vn n)) atTop (𝓝 (D ψ)) := by
    simpa only [hdvn, Function.comp_def] using
      (continuous_snd.tendsto ((ψ : H), D ψ)).comp hwlim
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp ((U.continuous.tendsto (ψ : H)).comp hv)).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hdae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      (((V.continuous.tendsto (D ψ)).comp hdv).comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hg (n : ℕ) : ∀ᵐ q ∂μ,
      (unitaryFiber U (vn n : H) q, unitaryFiber V (D (vn n)) q) ∈ (C q).graph :=
    hcore ⟨un n, (un n).property.1⟩
  filter_upwards [hC, hae, hdae, ae_all_iff.mpr hg] with q hc hq hdq hgq
  exact hc.mem_of_tendsto ((hq.comp hms.tendsto_atTop).prodMk_nhds hdq)
    (Eventually.of_forall (fun n => hgq (ns (ms n))))

/-- Universal graph descriptions, such as weak derivatives or pointwise
unbounded fibre actions, transfer to the product representatives. Only
core intertwinings are supplied. Full-domain slicing is the conclusion. -/
theorem product_relation_of_hasCore
    (Uc : H ≃ₗᵢ[ℂ] Lp (Lp K 2 ν) 2 μ)
    (Vc : H' ≃ₗᵢ[ℂ] Lp (Lp K' 2 ν) 2 μ)
    (Up : H ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (Vp : H' ≃ₗᵢ[ℂ] Lp K' 2 (μ.prod ν))
    (hU : ∀ v, ∀ᵐ q ∂μ, (fun x => unitaryFiber Uc v q x) =ᵐ[ν]
      (fun x => Up v (q, x)))
    (hV : ∀ v, ∀ᵐ q ∂μ, (fun x => unitaryFiber Vc v q x) =ᵐ[ν]
      (fun x => Vp v (q, x)))
    (D : H →ₗ.[ℂ] H') (hD : D.IsClosed)
    (C : Q → Lp K 2 ν →ₗ.[ℂ] Lp K' 2 ν) (hC : ∀ᵐ q ∂μ, (C q).IsClosed)
    (S : Submodule ℂ H) (hS : D.HasCore S)
    (hcore : ∀ ψ : S, ∀ᵐ q ∂μ,
      (unitaryFiber Uc (ψ : H) q,
        unitaryFiber Vc (D ⟨ψ, hS.le_domain ψ.property⟩) q) ∈ (C q).graph)
    (Rel : Q → (X → K) → (X → K') → Prop)
    (realize : ∀ q (u : Lp K 2 ν) (v : Lp K' 2 ν),
      (u, v) ∈ (C q).graph → Rel q u v)
    (congr : ∀ q u v u' v', u =ᵐ[ν] u' → v =ᵐ[ν] v' → Rel q u v → Rel q u' v')
    (ψ : D.domain) :
    ∀ᵐ q ∂μ, Rel q (fun x => Up (ψ : H) (q, x)) (fun x => Vp (D ψ) (q, x)) := by
  filter_upwards [unitary_closed_graph_between_of_hasCore Uc Vc D hD C hC S hS hcore ψ,
    hU (ψ : H), hV (D ψ)] with q hq hu hv
  exact congr q _ _ _ _ hu hv (realize q _ _ hq)

end GptLean.Gaussian
