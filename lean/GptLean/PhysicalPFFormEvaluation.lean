import GptLean.PhysicalFockHardOperators
import GptLean.PhysicalPFVacuumEnergy
import GptLean.PhysicalFreeHilbert
import GptLean.Repair.ChannelFormEvaluation

/-!
The ordinary PF evaluation formula for the constructed normal form and
the maximal physical field graphs. The reference vector is constructed
from raw weak derivatives, the radiation graph and the potential graph.
Restriction to the hard fiber then gives the same formula for the actual
pulled-back hard form.
-/

noncomputable section

namespace GptLean.PhysicalPFFormEvaluation

open MeasureTheory Filter Topology PhysicalFock PhysicalPFReference
  PhysicalNormalTrace PhysicalPFVacuumInsertion PhysicalPFVacuumEnergy
  PhotonLocalization Repair
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section Reference

variable (I : Type) [Fintype I] [DecidableEq I] (V : Position I → ℝ)

/-- Add the actual potential graph to an arbitrary actual free vector. -/
def referenceOfFree (v : SpatialFreeVector (I := I) radiationRoot)
    (p : WaveSpace I) (hp : ∀ᵐ x ∂volume, p x = (Real.sqrt (V x) : ℂ) • v.value x) :
    Reference I V :=
  ⟨(PhysicalFreeReferenceCore.electronic I (PhysicalFreeHilbert.ofVector I v),
      PhysicalFreeReferenceCore.radiationSource I (PhysicalFreeHilbert.ofVector I v),
      ⟨(v.value, p), hp⟩), by
    apply Prod.ext
    · exact (PhysicalFreeHilbert.ofVector I v).property
    · exact sub_self v.value⟩

theorem referenceOfFree_value (v : SpatialFreeVector (I := I) radiationRoot)
    (p : WaveSpace I) (hp) :
    inclusion I V (referenceOfFree I V v p hp) = v.value := rfl

theorem referenceOfFree_ordinary (v : SpatialFreeVector (I := I) radiationRoot)
    (p : WaveSpace I) (hp) (i : I) :
    ordinary I V i (referenceOfFree I V v p hp) = v.derivative i := rfl

theorem referenceOfFree_radiation (v : SpatialFreeVector (I := I) radiationRoot)
    (p : WaveSpace I) (hp) :
    radiation I V (referenceOfFree I V v p hp) = v.radiation :=
  PhysicalFreeHilbert.radiation_ofVector I v

theorem referenceOfFree_potential (v : SpatialFreeVector (I := I) radiationRoot)
    (p : WaveSpace I) (hp) :
    potential I V (referenceOfFree I V v p hp) = p := rfl

end Reference

section Integrals

variable {X H I : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem smul_sub_ae (d a : Lp H 2 μ) (df af : X → H)
    (hd : d =ᵐ[μ] df) (ha : a =ᵐ[μ] af) (c e : ℂ) :
    c • d - e • a =ᵐ[μ] fun x => c • df x - e • af x := by
  filter_upwards [Lp.coeFn_sub (c • d) (e • a), Lp.coeFn_smul c d,
    Lp.coeFn_smul e a, hd, ha] with x hsub hcd hea hdf haf
  simp only [hsub, hcd, hea, Pi.sub_apply, Pi.smul_apply, hdf, haf]

private theorem norm_sq_integral_ae (u : Lp H 2 μ) (f : X → H)
    (h : u =ᵐ[μ] f) : ‖u‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral]
  apply integral_congr_ae
  exact h.mono (fun _ hx => congrArg (fun v : H => ‖v‖ ^ 2) hx)

private theorem energy_integral (d : I → Lp H 2 μ) (r p : Lp H 2 μ)
    (df : I → X → H) (rest : X → WithLp 2 (H × H))
    (hd : ∀ i, d i =ᵐ[μ] df i)
    (hr : r =ᵐ[μ] fun x => (rest x).fst)
    (hp : p =ᵐ[μ] fun x => (rest x).snd) :
    (1 / 2 : ℝ) * ∑ i, ‖d i‖ ^ 2 + ‖r‖ ^ 2 + ‖p‖ ^ 2 =
      (∫ x, 1 / 2 * ∑ i, ‖df i x‖ ^ 2 ∂μ) + (∫ x, ‖rest x‖ ^ 2 ∂μ) := by
  have hi (i : I) : Integrable (fun x => ‖df i x‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (d i))).mp
      (Lp.memLp (d i))).congr ((hd i).mono (fun _ hx => congrArg (fun v : H => ‖v‖ ^ 2) hx))
  have hr' : Integrable (fun x => ‖(rest x).fst‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable r)).mp
      (Lp.memLp r)).congr (hr.mono (fun _ hx => congrArg (fun v : H => ‖v‖ ^ 2) hx))
  have hp' : Integrable (fun x => ‖(rest x).snd‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable p)).mp
      (Lp.memLp p)).congr (hp.mono (fun _ hx => congrArg (fun v : H => ‖v‖ ^ 2) hx))
  have hd' (i : I) := norm_sq_integral_ae (d i) (df i) (hd i)
  simp_rw [hd', norm_sq_integral_ae r _ hr,
    norm_sq_integral_ae p _ hp, WithLp.prod_norm_sq_eq_of_L2]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hi i),
    integral_add hr' hp']
  ring

end Integrals

attribute [local irreducible] PhysicalPFReference.normalEnergy PhysicalPFVacuumInsertion.insertion

-- Align concrete operator modules with their direct normed-space parents.
local instance formPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance formPhotonRestDirectInner : InnerProductSpace ℂ (WithLp 2 (PhotonFock × PhotonFock)) :=
  { (inferInstance : InnerProductSpace ℂ (WithLp 2 (PhotonFock × PhotonFock))) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (WithLp 2 (PhotonFock × PhotonFock))) }

section Ambient

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (k : I → Position I → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (e : ℝ)

set_option backward.isDefEq.respectTransparency.types true in
theorem reference_field_ae_of_graph (u : Reference I V)
    (f af : Position I → PhotonFock) (i : I)
    (hu : inclusion I V u =ᵐ[volume] f)
    (hgraph : ∀ᵐ x ∂volume, (f x, af x) ∈
      (segalOperator photonMeasure (k i x).val.1).graph) :
    field I V C k hk M hM i u =ᵐ[volume] af := by
  have hq : ∀ᵐ x ∂volume, radiationGraphInclusion (radiationSource I V u x) = f x := by
    exact (reference_radiation_ae I V u).symm.trans hu
  filter_upwards [spatialField_ae volume C (k i) (hk i) M (hM i) (radiationSource I V u),
    hgraph, hq] with x hx hg hq
  have hvalue : field I V C k hk M hM i u x =
      kernelField C (k i x) (radiationSource I V u x) := hx
  have hkernel : SegalGraph photonMeasure (k i x).val.1 (f x)
      (kernelField C (k i x) (radiationSource I V u x)) :=
    (congrArg (fun z : PhotonFock => SegalGraph photonMeasure (k i x).val.1 z
      (kernelField C (k i x) (radiationSource I V u x))) hq).mp
        (kernelField_segalGraph C (k i x) (radiationSource I V u x))
  exact hvalue.trans (segalGraph_unique photonMeasure (k i x).val.1 hkernel
    ((segalOperator_graph_iff photonMeasure _ _ _).mp hg))

theorem reference_covariant_ae (u : Reference I V)
    (df af : I → Position I → PhotonFock)
    (hd : ∀ i, ordinary I V i u =ᵐ[volume] df i)
    (ha : ∀ i, field I V C k hk M hM i u =ᵐ[volume] af i) (i : I) :
    covariant I V C k hk M hM e i u =ᵐ[volume]
      fun x => -Complex.I • df i x - (e : ℂ) • af i x := by
  have h := smul_sub_ae (H := PhotonFock) (μ := volume)
    (ordinary I V i u) (field I V C k hk M hM i u) (df i) (af i)
    (hd i) (ha i) (-Complex.I) (e : ℂ)
  exact (congrArg (fun z : WaveSpace I => z =ᵐ[volume]
    fun x => -Complex.I • df i x - (e : ℂ) • af i x)
      (covariant_apply I V C k hk M hM e i u)).mpr h

set_option backward.isDefEq.respectTransparency.types true in
theorem fullFormEvaluation :
    HasPFFormEvaluation (I := I) (H := PhotonFock)
      (F := WithLp 2 (PhotonFock × PhotonFock)) radiationRoot
      (fun i x => segalOperator photonMeasure (k i x).val.1)
      (fun x => restOperator radiationRoot (Real.sqrt (V x) : ℂ)) e
      (fun v => (normalEnergy I V C k hk M hM B S e).expectation
        ((B.realization (WaveSpace I)).rank.rankOne v)) := by
  intro f df af bf hf _href hweak hdf haf hfield hbf hrest
  let rf := fun x => (bf x).fst
  let pf := fun x => (bf x).snd
  have hrf : MemLp rf 2 volume := (WithLp.fstL 2 ℂ PhotonFock PhotonFock).comp_memLp' hbf
  have hpf : MemLp pf 2 volume := (WithLp.sndL 2 ℂ PhotonFock PhotonFock).comp_memLp' hbf
  let v : SpatialFreeVector (I := I) radiationRoot :=
    { value := hf.toLp f
      derivative := fun i => (hdf i).toLp (df i)
      radiation := hrf.toLp rf
      weak := hweak.congr hf.coeFn_toLp.symm (fun i => (hdf i).coeFn_toLp.symm)
      radiation_graph := by
        filter_upwards [hf.coeFn_toLp, hrf.coeFn_toLp, hrest] with x hx hr hgraph
        rw [hx, hr]
        exact ((restOperator_graph_iff radiationRoot _ _ _).mp hgraph).1 }
  have hp : ∀ᵐ x ∂volume, hpf.toLp pf x = (Real.sqrt (V x) : ℂ) • v.value x := by
    filter_upwards [hpf.coeFn_toLp, hf.coeFn_toLp, hrest] with x hpx hfx hgraph
    change hpf.toLp pf x = (Real.sqrt (V x) : ℂ) • hf.toLp f x
    rw [hpx, hfx]
    exact ((restOperator_graph_iff radiationRoot _ _ _).mp hgraph).2
  let u := referenceOfFree I V v (hpf.toLp pf) hp
  have hu : inclusion I V u = hf.toLp f := rfl
  have hrad : radiation I V u = hrf.toLp rf := referenceOfFree_radiation I V v _ hp
  have hpot : potential I V u = hpf.toLp pf := rfl
  have hd (i : I) : ordinary I V i u = (hdf i).toLp (df i) := rfl
  have ha (i : I) : field I V C k hk M hM i u = (haf i).toLp (af i) := by
    apply Lp.ext
    have hvalue : inclusion I V u =ᵐ[volume] f :=
      (congrArg (fun z : WaveSpace I => z =ᵐ[volume] f) hu).mpr hf.coeFn_toLp
    exact (reference_field_ae_of_graph I V C k hk M hM u f (af i) i hvalue
      (hfield i)).trans (haf i).coeFn_toLp.symm
  have hcov (i : I) : covariant I V C k hk M hM e i u =ᵐ[volume]
      fun x => -Complex.I • df i x - (e : ℂ) • af i x := by
    exact reference_covariant_ae I V C k hk M hM e u df af
      (fun j => (congrArg (fun z : WaveSpace I => z =ᵐ[volume] df j) (hd j)).mpr
        (hdf j).coeFn_toLp)
      (fun j => (congrArg (fun z : WaveSpace I => z =ᵐ[volume] af j) (ha j)).mpr
        (haf j).coeFn_toLp) i
  have he := energy_integral (fun i => covariant I V C k hk M hM e i u)
    (radiation I V u) (potential I V u)
    (fun i x => -Complex.I • df i x - (e : ℂ) • af i x) bf hcov
    (by rw [hrad]; exact hrf.coeFn_toLp) (by rw [hpot]; exact hpf.coeFn_toLp)
  have hnormal := normalEnergy_rankOne I V C k hk M hM B S e u
  have htransport := congrArg (fun z : WaveSpace I =>
    (normalEnergy I V C k hk M hM B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne z)) hu
  exact htransport.symm.trans (hnormal.trans (congrArg ENNReal.ofReal he))

end Ambient

section Pullback

variable {I H K F G : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

omit [CompleteSpace H] [CompleteSpace K] in
private theorem norm_covariant_map (J : H →ₗᵢ[ℂ] K) (e : ℝ) (d a : H) :
    ‖-Complex.I • J d - (e : ℂ) • J a‖ ^ 2 =
      ‖-Complex.I • d - (e : ℂ) • a‖ ^ 2 := by
  simpa only [map_sub, map_smul] using
    congrArg (fun r : ℝ => r ^ 2) (J.norm_map (-Complex.I • d - (e : ℂ) • a))

omit [CompleteSpace H] [CompleteSpace K] in
private theorem rest_graph_map (J : H →ₗᵢ[ℂ] K)
    (R : H →ₗ.[ℂ] H) (R' : K →ₗ.[ℂ] K)
    (hR : ∀ u v, (u, v) ∈ R.graph → (J u, J v) ∈ R'.graph)
    (a : ℂ) (u : H) (v : WithLp 2 (H × H))
    (hv : (u, v) ∈ (restOperator R a).graph) :
    (J u, J.withLpProdMap 2 J v) ∈ (restOperator R' a).graph := by
  apply (restOperator_graph_iff R' a _ _).mpr
  change (J u, J v.fst) ∈ R'.graph ∧ J v.snd = a • J u
  obtain ⟨hr, hp⟩ := (restOperator_graph_iff R a u v).mp hv
  exact ⟨hR u v.fst hr, (congrArg J hp).trans (J.map_smul a u)⟩

set_option backward.isDefEq.respectTransparency.types true in
/-- Isometric transport of a proved ordinary form formula. -/
theorem formEvaluation_pullback (J : H →ₗᵢ[ℂ] K) (L : F →ₗᵢ[ℂ] G)
    (R : H →ₗ.[ℂ] H) (R' : K →ₗ.[ℂ] K)
    (A : I → EuclideanSpace ℝ I → H →ₗ.[ℂ] H)
    (A' : I → EuclideanSpace ℝ I → K →ₗ.[ℂ] K)
    (D : EuclideanSpace ℝ I → H →ₗ.[ℂ] F)
    (D' : EuclideanSpace ℝ I → K →ₗ.[ℂ] G)
    (hR : ∀ u v, (u, v) ∈ R.graph → (J u, J v) ∈ R'.graph)
    (hA : ∀ i x u v, (u, v) ∈ (A i x).graph → (J u, J v) ∈ (A' i x).graph)
    (hD : ∀ x u v, (u, v) ∈ (D x).graph → (J u, L v) ∈ (D' x).graph)
    (e : ℝ) (q : Lp K 2 (volume : Measure (EuclideanSpace ℝ I)) → ℝ≥0∞)
    (hform : HasPFFormEvaluation (I := I) (H := K) (F := G) R' A' D' e q) :
    HasPFFormEvaluation (I := I) (H := H) (F := F) R A D e (fun v => q (spatialLift volume J v)) := by
  intro f df af bf hf href hweak hdf haf hfield hbf hrest
  have hf' := J.toContinuousLinearMap.comp_memLp' hf
  have hd' (i : I) := J.toContinuousLinearMap.comp_memLp' (hdf i)
  have ha' (i : I) := J.toContinuousLinearMap.comp_memLp' (haf i)
  have hb' := L.toContinuousLinearMap.comp_memLp' hbf
  have hw' := weakH1Local_map (J.toContinuousLinearMap.restrictScalars ℝ) hweak
  have href' : InPFReferenceDomain R' (J ∘ f) := by
    obtain ⟨_, _, r, _, _, hr, hrad⟩ := href
    refine ⟨hf', fun i => J ∘ df i, J ∘ r, hw', hd',
      J.toContinuousLinearMap.comp_memLp' hr, ?_⟩
    exact hrad.mono (fun x hx => hR _ _ hx)
  have heval := hform (J ∘ f) (fun i => J ∘ df i) (fun i => J ∘ af i) (L ∘ bf)
    hf' href' hw' hd' ha' (fun i => (hfield i).mono (fun x hx => hA i x _ _ hx))
    hb' (hrest.mono (fun x hx => hD x _ _ hx))
  have hv : hf'.toLp (J ∘ f) = spatialLift volume J (hf.toLp f) := by
    apply Lp.ext
    filter_upwards [hf'.coeFn_toLp, hf.coeFn_toLp,
      spatialLift_ae volume J (hf.toLp f)] with x hx hf hs
    exact hx.trans (by rw [hs, hf]; rfl)
  have hkin :
      (∫ x, (1 / 2 : ℝ) * ∑ i, ‖-Complex.I • J (df i x) - (e : ℂ) • J (af i x)‖ ^ 2) =
        ∫ x, (1 / 2 : ℝ) * ∑ i, ‖-Complex.I • df i x - (e : ℂ) • af i x‖ ^ 2 := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => congrArg (fun r : ℝ => (1 / 2 : ℝ) * r)
      (Finset.sum_congr rfl (fun i _ => norm_covariant_map J e (df i x) (af i x)))
  have hrestNorm : (∫ x, ‖L (bf x)‖ ^ 2) = ∫ x, ‖bf x‖ ^ 2 :=
    integral_congr_ae (ae_of_all _ fun x =>
      congrArg (fun r : ℝ => r ^ 2) (L.norm_map (bf x)))
  exact (congrArg q hv).symm.trans (heval.trans
    (congrArg ENNReal.ofReal (congrArg₂ (fun a b : ℝ => a + b) hkin hrestNorm)))

end Pullback

section Hard

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (h : I → Position I → WeightedPhotonKernel)
  (hh : ∀ i, AEStronglyMeasurable (h i) volume)
  (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂volume, ‖h i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (BF : StandardSymmetricFockExponential) (c e : ℝ)

local instance formHardDirectInner :
    InnerProductSpace ℂ (generatedFockSubspace (hardOnePhoton c)) :=
  { (inferInstance : InnerProductSpace ℂ (generatedFockSubspace (hardOnePhoton c))) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (generatedFockSubspace (hardOnePhoton c))) }

local instance formHardRestDirectInner : InnerProductSpace ℂ
    (WithLp 2 (generatedFockSubspace (hardOnePhoton c) × generatedFockSubspace (hardOnePhoton c))) :=
  { (inferInstance : InnerProductSpace ℂ
      (WithLp 2 (generatedFockSubspace (hardOnePhoton c) × generatedFockSubspace (hardOnePhoton c)))) with
    toNormedSpace := (inferInstance : NormedSpace ℂ
      (WithLp 2 (generatedFockSubspace (hardOnePhoton c) × generatedFockSubspace (hardOnePhoton c)))) }

set_option backward.isDefEq.respectTransparency.types true in
theorem hardFormEvaluation :
    HasPFFormEvaluation (I := I) (H := generatedFockSubspace (hardOnePhoton c))
      (F := WithLp 2 (generatedFockSubspace (hardOnePhoton c) × generatedFockSubspace (hardOnePhoton c)))
      (hardRadiationOperator c)
      (fun i x => hardFieldOperator c (h i x).val.1)
      (fun x => hardRestOperator c (Real.sqrt (V x) : ℂ)) e
      (fun v => (hardEnergy I V C h hh M hM B S BF c e).expectation
        ((B.realization (Lp (generatedFockSubspace (hardOnePhoton c)) 2
          (volume : Measure (Position I)))).rank.rankOne v)) := by
  let J : generatedFockSubspace (hardOnePhoton c) →ₗᵢ[ℂ] PhotonFock :=
    (generatedFockSubspace (hardOnePhoton c)).subtypeₗᵢ
  let L : WithLp 2 (generatedFockSubspace (hardOnePhoton c) × generatedFockSubspace (hardOnePhoton c))
      →ₗᵢ[ℂ] WithLp 2 (PhotonFock × PhotonFock) := J.withLpProdMap 2 J
  have hform := formEvaluation_pullback
    (I := I) (H := generatedFockSubspace (hardOnePhoton c)) (K := PhotonFock)
    (F := WithLp 2 (generatedFockSubspace (hardOnePhoton c) × generatedFockSubspace (hardOnePhoton c)))
    (G := WithLp 2 (PhotonFock × PhotonFock)) J L (hardRadiationOperator c) radiationRoot
    (fun i x => hardFieldOperator c (h i x).val.1)
    (fun i x => segalOperator photonMeasure (h i x).val.1)
    (fun x => hardRestOperator c (Real.sqrt (V x) : ℂ))
    (fun x => restOperator radiationRoot (Real.sqrt (V x) : ℂ))
    (fun u v huv => (hardRadiationOperator_graph_iff c u v).mp huv)
    (fun i x u v huv =>
      (segalOperator_graph_iff photonMeasure _ _ _).mpr
        ((hardFieldOperator_graph_iff c _ u v).mp huv))
    (fun x u v huv => rest_graph_map
      (H := generatedFockSubspace (hardOnePhoton c)) (K := PhotonFock)
      J (hardRadiationOperator c) radiationRoot
      (fun a b hab => (hardRadiationOperator_graph_iff c a b).mp hab)
      (Real.sqrt (V x) : ℂ) u v huv)
    e (fun v => (normalEnergy I V C h hh M hM B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne v))
    (fullFormEvaluation I V C h hh M hM B S e)
  have heq (v : Lp (generatedFockSubspace (hardOnePhoton c)) 2
      (volume : Measure (Position I))) :
      (hardEnergy I V C h hh M hM B S BF c e).expectation
          ((B.realization (Lp (generatedFockSubspace (hardOnePhoton c)) 2
            (volume : Measure (Position I)))).rank.rankOne v) =
        (normalEnergy I V C h hh M hM B S e).expectation
          ((B.realization (WaveSpace I)).rank.rankOne (spatialLift volume J v)) := by
    have hv : insertion volume BF c v = spatialLift volume J v := by
      apply Lp.ext
      filter_upwards [insertion_ae volume BF c v, spatialLift_ae volume J v] with x hi hj
      exact hi.trans hj.symm
    exact (hardEnergy_rankOne I V C h hh M hM B S BF c e v).trans
      (congrArg (fun w : WaveSpace I =>
        (normalEnergy I V C h hh M hM B S e).expectation
          ((B.realization (WaveSpace I)).rank.rankOne w)) hv)
  exact (congrArg (fun q => HasPFFormEvaluation (I := I)
    (H := generatedFockSubspace (hardOnePhoton c))
    (F := WithLp 2 (generatedFockSubspace (hardOnePhoton c) × generatedFockSubspace (hardOnePhoton c)))
    (hardRadiationOperator c)
    (fun i x => hardFieldOperator c (h i x).val.1)
    (fun x => hardRestOperator c (Real.sqrt (V x) : ℂ)) e q) (funext heq)).mpr hform

end Hard

end GptLean.PhysicalPFFormEvaluation
