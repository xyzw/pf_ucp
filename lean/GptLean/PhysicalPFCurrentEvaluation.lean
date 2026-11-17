import GptLean.PhysicalPFFormEvaluation
import GptLean.PhysicalCoulombReferenceCore
import GptLean.RemovalPhysicalCurrent

/-!
Canonical tested current on the actual Coulomb PF domain. The Coulomb
graph theorem supplies the potential coordinate for every free H1 and
radiation vector. The same current formula is transported to the hard
fiber using the actual vacuum insertion.
-/

noncomputable section

namespace GptLean.PhysicalPFCurrentEvaluation

open MeasureTheory Filter Topology PhysicalFock PhysicalPFReference
  PhysicalNormalTrace PhysicalPFSource PhysicalPFVacuumInsertion PhysicalPFVacuumEnergy
  PhysicalPFFormEvaluation PhotonLocalization Repair RemovalState RemovalPhysicalCurrent
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] PhysicalPFReference.normalEnergy

private theorem multiplier_inner_ae {X H : Type*} [MeasurableSpace X]
    {μ : Measure X} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (A : ℝ) (hA : ∀ᵐ x ∂μ, |a x| ≤ A)
    (u v : Lp H 2 μ) (f d : X → H) (hu : u =ᵐ[μ] f) (hd : v =ᵐ[μ] d) :
    (inner ℂ u (realL2Multiplier a ha A hA v)).re =
      (∫ x, inner ℂ (f x) ((a x : ℂ) • d x) ∂μ).re := by
  rw [L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [hu, hd, realL2Multiplier_apply a ha A hA v] with x hu hd hm
  simp only [hu, hm, hd, Complex.coe_smul]

private theorem tendsto_eval_transport {T : Type*} (f : ℕ → T → ℝ)
    (x y : T) (a b : ℝ) (hxy : x = y) (hab : a = b)
    (h : Tendsto (fun n => f n x) atTop (𝓝 a)) :
    Tendsto (fun n => f n y) atTop (𝓝 b) := by
  simpa only [← hxy, ← hab] using h

section Definition

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (k : I → Position I → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (e : ℝ)

def testedCurrent (a : Position I → ℝ) (ha : AEStronglyMeasurable a volume)
    (A : ℝ) (hA : ∀ᵐ x ∂volume, |a x| ≤ A) (i : I) :
    FormObservable (normalEnergy I V C k hk M hM B S e) :=
  observable I V C k hk M hM B S e (inclusion I V)
    ((realL2Multiplier a ha A hA).comp (covariant I V C k hk M hM e i))

theorem testedCurrent_reference (a : Position I → ℝ) (ha : AEStronglyMeasurable a volume)
    (A : ℝ) (hA : ∀ᵐ x ∂volume, |a x| ≤ A) (i : I) (u : Reference I V)
    (f d : Position I → PhotonFock)
    (hu : inclusion I V u =ᵐ[volume] f)
    (hd : covariant I V C k hk M hM e i u =ᵐ[volume] d) :
    (testedCurrent I V C k hk M hM B S e a ha A hA i).value
      ((B.realization (WaveSpace I)).rank.rankOne (inclusion I V u)) =
        (∫ x, ⟪f x, (a x : ℂ) • d x⟫_ℂ).re := by
  exact (observable_rankOne I V C k hk M hM B S e (inclusion I V)
    ((realL2Multiplier a ha A hA).comp (covariant I V C k hk M hM e i)) u).trans
      (multiplier_inner_ae (H := PhotonFock) (μ := volume) a ha A hA
        (inclusion I V u) (covariant I V C k hk M hM e i u) f d hu hd)

theorem testedCurrent_source_hasSum {x : B.Trace (WaveSpace I)} (s : Source I V B x)
    (he : (normalEnergy I V C k hk M hM B S e).expectation x < ⊤)
    (a : Position I → ℝ) (ha : AEStronglyMeasurable a volume)
    (A : ℝ) (hA : ∀ᵐ z ∂volume, |a z| ≤ A) (i : I) :
    HasSum (fun n => ∫ z, a z * (inner ℂ (inclusion I V (s.vector n) z)
      (covariant I V C k hk M hM e i (s.vector n) z)).re)
      ((testedCurrent I V C k hk M hM B S e a ha A hA i).value x) :=
  s.tested_inner_hasSum C k hk M hM S e he (inclusion I V)
    (covariant I V C k hk M hM e i) a ha A hA

end Definition

section Coulomb

local instance currentPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }


variable {Test : Type*} (N : ℕ) (c : ℝ) (hc : 0 ≤ c)
  (C : CanonicalSectorCCR photonMeasure)
  (k : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (e : ℝ) (weight : Test → Position (Fin N × Fin 3) → ℝ)
  (hw : ∀ t, AEStronglyMeasurable (weight t) volume)
  (A : Test → ℝ) (hA : ∀ t, ∀ᵐ x ∂volume, |weight t x| ≤ A t)
  (direction : Test → Fin N × Fin 3)

set_option backward.isDefEq.respectTransparency.types true in
include hc in
theorem fullCanonicalCurrent :
    CanonicalCurrent (I := Fin N × Fin 3) (H := PhotonFock) (Test := Test)
      (B.realization (WaveSpace (Fin N × Fin 3))).rank radiationRoot
      (fun i x => segalOperator photonMeasure (k i x).val.1) e
      (fun t => testedCurrent (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
        C k hk M hM B S e (weight t) (hw t) (A t) (hA t) (direction t)) weight direction := by
  intro t f df af hf href hweak hdf _haf hfield
  obtain ⟨_, _, r, _, _, hr, hrad⟩ := href
  let v : SpatialFreeVector (I := Fin N × Fin 3) radiationRoot :=
    { value := hf.toLp f
      derivative := fun i => (hdf i).toLp (df i)
      radiation := hr.toLp r
      weak := hweak.congr hf.coeFn_toLp.symm (fun i => (hdf i).coeFn_toLp.symm)
      radiation_graph := by
        filter_upwards [hf.coeFn_toLp, hr.coeFn_toLp, hrad] with x hf hr hg
        rw [hf, hr]
        exact hg }
  let V := fun x => c * PhysicalCoulombH1.potential N x
  let u : Reference (Fin N × Fin 3) V :=
    PhysicalCoulombReferenceCore.attach N c hc (PhysicalFreeHilbert.ofVector (Fin N × Fin 3) v)
  have hu : inclusion (Fin N × Fin 3) V u = hf.toLp f := rfl
  have hder (i : Fin N × Fin 3) : ordinary (Fin N × Fin 3) V i u =ᵐ[volume] df i :=
    (hdf i).coeFn_toLp
  have hval : inclusion (Fin N × Fin 3) V u =ᵐ[volume] f := by
    exact (congrArg (fun z : WaveSpace (Fin N × Fin 3) => z =ᵐ[volume] f) hu).mpr
      hf.coeFn_toLp
  have ha (i : Fin N × Fin 3) : field (Fin N × Fin 3) V C k hk M hM i u =ᵐ[volume] af i :=
    reference_field_ae_of_graph (Fin N × Fin 3) V C k hk M hM u f (af i) i hval (hfield i)
  have hcov := reference_covariant_ae (Fin N × Fin 3) V C k hk M hM e u df af hder ha (direction t)
  have hv := testedCurrent_reference (Fin N × Fin 3) V C k hk M hM B S e
    (weight t) (hw t) (A t) (hA t) (direction t) u f _ hval hcov
  have hfinite : (normalEnergy (Fin N × Fin 3) V C k hk M hM B S e).expectation
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne (inclusion (Fin N × Fin 3) V u)) < ⊤ := by
    exact (normalEnergy_rankOne (Fin N × Fin 3) V C k hk M hM B S e u).trans_lt
      ENNReal.ofReal_lt_top
  have hlimit := (testedCurrent (Fin N × Fin 3) V C k hk M hM B S e
    (weight t) (hw t) (A t) (hA t) (direction t)).converges _
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne_positive _) hfinite
  exact tendsto_eval_transport
    (fun n z => (testedCurrent (Fin N × Fin 3) V C k hk M hM B S e
      (weight t) (hw t) (A t) (hA t) (direction t)).approximation n z)
    _ _ _ _ (congrArg (B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne hu) hv hlimit

end Coulomb

section Transport

variable {I H K Test : Type} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem canonicalCurrent_pullback (B : StandardNormalTraceBackground)
    (J : H →ₗᵢ[ℂ] K)
    (R : H →ₗ.[ℂ] H) (R' : K →ₗ.[ℂ] K)
    (A : I → Position I → H →ₗ.[ℂ] H) (A' : I → Position I → K →ₗ.[ℂ] K)
    (hR : ∀ u v, (u, v) ∈ R.graph → (J u, J v) ∈ R'.graph)
    (hA : ∀ i x u v, (u, v) ∈ (A i x).graph → (J u, J v) ∈ (A' i x).graph)
    (E : PositiveForm (B.traceData (H := Lp K 2 (volume : Measure (Position I)))))
    (O : Test → FormObservable E) (e : ℝ)
    (weight : Test → Position I → ℝ) (direction : Test → I)
    (hcanonical : CanonicalCurrent
      (B.realization (Lp K 2 (volume : Measure (Position I)))).rank
      R' A' e O weight direction) :
    CanonicalCurrent (B.realization (Lp H 2 (volume : Measure (Position I)))).rank
      R A e (fun t => pullbackObservable B (spatialLift volume J).toContinuousLinearMap E (O t))
      weight direction := by
  intro t f df af hf href hweak hdf haf hfield
  have hf' := J.toContinuousLinearMap.comp_memLp' hf
  have hd' (i : I) := J.toContinuousLinearMap.comp_memLp' (hdf i)
  have ha' (i : I) := J.toContinuousLinearMap.comp_memLp' (haf i)
  have hw' := weakH1Local_map (J.toContinuousLinearMap.restrictScalars ℝ) hweak
  have href' : InPFReferenceDomain R' (J ∘ f) := by
    obtain ⟨_, _, r, _, _, hr, hrad⟩ := href
    refine ⟨hf', fun i => J ∘ df i, J ∘ r, hw', hd',
      J.toContinuousLinearMap.comp_memLp' hr, ?_⟩
    exact hrad.mono (fun x hx => hR _ _ hx)
  have heval := hcanonical t (J ∘ f) (fun i => J ∘ df i) (fun i => J ∘ af i)
    hf' href' hw' hd' ha' (fun i => (hfield i).mono (fun x hx => hA i x _ _ hx))
  have hv : hf'.toLp (J ∘ f) = spatialLift volume J (hf.toLp f) := by
    apply Lp.ext
    filter_upwards [hf'.coeFn_toLp, hf.coeFn_toLp,
      spatialLift_ae volume J (hf.toLp f)] with x hx hf hs
    exact hx.trans (by rw [hs, hf]; rfl)
  have he : (∫ x, inner ℂ ((J ∘ f) x)
      ((weight t x : ℂ) • (-Complex.I • (J ∘ df (direction t)) x -
        (e : ℂ) • (J ∘ af (direction t)) x))).re =
      (∫ x, inner ℂ (f x) ((weight t x : ℂ) •
        (-Complex.I • df (direction t) x - (e : ℂ) • af (direction t) x))).re := by
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp only [Function.comp_apply, ← map_smul, ← map_sub, J.inner_map_map]
  rw [hv, he] at heval
  change Tendsto (fun n => (O t).approximation n
    (B.push (spatialLift volume J).toContinuousLinearMap
      ((B.realization (Lp H 2 (volume : Measure (Position I)))).rank.rankOne (hf.toLp f))))
    atTop (𝓝 _)
  rw [B.push_rankOne]
  exact heval

end Transport

section Hard

attribute [local instance] currentPhotonDirectInner

local instance currentHardDirectInner (κ : ℝ) :
    InnerProductSpace ℂ (generatedFockSubspace (hardOnePhoton κ)) :=
  { (inferInstance : InnerProductSpace ℂ (generatedFockSubspace (hardOnePhoton κ))) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (generatedFockSubspace (hardOnePhoton κ))) }


variable {Test : Type} (N : ℕ) (c : ℝ) (hc : 0 ≤ c)
  (C : CanonicalSectorCCR photonMeasure)
  (h : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hh : ∀ i, AEStronglyMeasurable (h i) volume)
  (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂volume, ‖h i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (BF : StandardSymmetricFockExponential) (κ e : ℝ)
  (weight : Test → Position (Fin N × Fin 3) → ℝ)
  (hw : ∀ t, AEStronglyMeasurable (weight t) volume)
  (A : Test → ℝ) (hA : ∀ t, ∀ᵐ x ∂volume, |weight t x| ≤ A t)
  (direction : Test → Fin N × Fin 3)

set_option backward.isDefEq.respectTransparency.types true in
def hardTestedCurrent (t : Test) :
    FormObservable (hardEnergy (Fin N × Fin 3)
      (fun x => c * PhysicalCoulombH1.potential N x) C h hh M hM B S BF κ e) :=
  pullbackObservable
    (H := Lp (generatedFockSubspace (hardOnePhoton κ)) 2
      (volume : Measure (Position (Fin N × Fin 3))))
    (K := WaveSpace (Fin N × Fin 3)) B (insertion volume BF κ).toContinuousLinearMap
    (normalEnergy (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
      C h hh M hM B S e)
    (testedCurrent (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
      C h hh M hM B S e (weight t) (hw t) (A t) (hA t) (direction t))

set_option backward.isDefEq.respectTransparency.types true in
include hc in
theorem hardCanonicalCurrent :
    CanonicalCurrent (I := Fin N × Fin 3)
      (H := generatedFockSubspace (hardOnePhoton κ)) (Test := Test)
      (B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2
        (volume : Measure (Position (Fin N × Fin 3))))).rank
      (hardRadiationOperator κ) (fun i x => hardFieldOperator κ (h i x).val.1) e
      (hardTestedCurrent N c C h hh M hM B S BF κ e weight hw A hA direction)
      weight direction := by
  apply canonicalCurrent_pullback (I := Fin N × Fin 3) (Test := Test)
    (H := generatedFockSubspace (hardOnePhoton κ)) (K := PhotonFock)
    (E := normalEnergy (Fin N × Fin 3) (fun x => c * PhysicalCoulombH1.potential N x)
      C h hh M hM B S e)
    (O := fun t => testedCurrent (Fin N × Fin 3)
      (fun x => c * PhysicalCoulombH1.potential N x) C h hh M hM B S e
      (weight t) (hw t) (A t) (hA t) (direction t))
    (e := e) (weight := weight) (direction := direction)
    B (hardPhotonVacuumEmbedding BF κ)
    (hardRadiationOperator κ) radiationRoot
    (fun i x => hardFieldOperator κ (h i x).val.1)
    (fun i x => segalOperator photonMeasure (h i x).val.1)
  · intro u v huv
    have hgraph := (hardRadiationOperator_graph_iff κ u v).mp huv
    exact (congrArg₂ (fun a b : PhotonFock => (a, b) ∈ radiationRoot.graph)
      (hardPhotonVacuumEmbedding_apply BF κ u)
      (hardPhotonVacuumEmbedding_apply BF κ v)).mpr hgraph
  · intro i x u v huv
    have hgraph := (segalOperator_graph_iff photonMeasure (h i x).val.1 u.val v.val).mpr
      ((hardFieldOperator_graph_iff κ (h i x).val.1 u v).mp huv)
    exact (congrArg₂ (fun a b : PhotonFock =>
      (a, b) ∈ (segalOperator photonMeasure (h i x).val.1).graph)
      (hardPhotonVacuumEmbedding_apply BF κ u)
      (hardPhotonVacuumEmbedding_apply BF κ v)).mpr hgraph
  · exact fullCanonicalCurrent N c hc C h hh M hM B S e weight hw A hA direction

end Hard

end GptLean.PhysicalPFCurrentEvaluation
