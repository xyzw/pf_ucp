import GptLean.PhysicalGaussianPFSource
import GptLean.PhysicalGaussianH1
import GptLean.PhysicalGaussianSpatialGraph
import GptLean.PhysicalGaussianParticleField
import GptLean.PhysicalPFVacuumEnergy

/-!
The physical reference vectors supply the original PF data required by
infrared removal. Every Gaussian graph and weak derivative is derived
from the actual reference vector and the same Gaussian unitary.
-/

noncomputable section
namespace GptLean.PhysicalPFSource

open MeasureTheory Filter PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalGaussianCoordinates PhysicalPolarization
  RemovalSource RemovalEnergy Gaussian SymmetricLift
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

private theorem map_covariant_split {E G : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup G] [Module ℂ G]
    (L : E →ₗ[ℂ] G) {c h d a s : E} (t : ℂ)
    (hc : c = h - t • s) (hh : h = (-Complex.I) • d - t • a) :
    L c = ((-Complex.I) • L d - t • L a) - t • L s := by
  rw [hc, hh, map_sub, map_sub, map_smul, map_smul, map_smul]

private theorem lp_covariant_of_soft {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {μ : Measure X}
    (d a s u : Lp H 2 μ) (e : ℝ) (b : X → ℝ)
    (hs : s =ᵐ[μ] fun x => (b x : ℂ) • u x) :
    ((-Complex.I) • d - (e : ℂ) • a) - (e : ℂ) • s =ᵐ[μ]
      fun x => -Complex.I • d x - (e : ℂ) • a x - ((e * b x : ℝ) : ℂ) • u x := by
  filter_upwards [hs, Lp.coeFn_sub ((-Complex.I) • d - (e : ℂ) • a) ((e : ℂ) • s),
    Lp.coeFn_sub ((-Complex.I) • d) ((e : ℂ) • a), Lp.coeFn_smul (-Complex.I) d,
    Lp.coeFn_smul (e : ℂ) a, Lp.coeFn_smul (e : ℂ) s] with x hsx hout hin hd ha hsmul
  simp only [Pi.sub_apply, Pi.smul_apply] at hout hin hd ha hsmul
  rw [hout, hin, hd, ha, hsmul, hsx, smul_smul, ← Complex.ofReal_mul]

variable {N : ℕ} (V : Position (Fin N × Fin 3) → ℝ)
  (F : Frame) (χ : ArticleCutoff) (κ : ℝ) (hκ : 0 ≤ κ)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) (F.softRealStructure κ))
  (B : StandardNormalTraceBackground)

local instance pfGraphsHardNormedAddCommGroup : NormedAddCommGroup (HardPhotonFock κ) :=
  Submodule.normedAddCommGroup (𝕜 := ℂ) (E := PhotonFock) (HardPhotonFock κ)

local instance pfGraphsPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance pfGraphsHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

attribute [local irreducible] photonGaussianUnitary

set_option backward.isDefEq.respectTransparency.types true in
theorem gaussianReference_radiation_graph (u : Reference (Fin N × Fin 3) V) :
    ∀ᵐ qx ∂W.space.measure.prod volume,
      (photonGaussianSource BF κ W N (inclusion (Fin N × Fin 3) V u) qx,
        photonGaussianSource BF κ W N (hardReference V C B BF κ W u) qx) ∈
          (hardRadiationOperator κ).graph := by
  apply productSource_closed_relation
    (X := Configuration N) (Q := W.space.Q)
    (H := PhotonFock) (H' := PhotonFock)
    (K := HardPhotonFock κ) (K' := HardPhotonFock κ)
    volume W.space.measure
    (photonGaussianUnitary BF κ W) (photonGaussianUnitary BF κ W)
    ((hardRadiationOperator κ).graph : Set (HardPhotonFock κ × HardPhotonFock κ))
    (hardRadiationOperator_closed κ)
  have hi := PhysicalPFVacuumEnergy.reference_radiation_ae (Fin N × Fin 3) V u
  filter_upwards [hi, (hardGaussianRoot B.normal (B.realization PhotonFock).functional
    BF C κ W).coeFn_compLpL (radiationSource (Fin N × Fin 3) V u)] with x hix hrx
  change hardReference V C B BF κ W u x = _ at hrx
  have hpoint := hardGaussianRoot_graph B.normal (B.realization PhotonFock).functional BF C κ W
    (radiationSource (Fin N × Fin 3) V u x)
  exact (congrArg₂ (fun a b : PhotonFock =>
    ∀ᵐ q ∂W.space.measure,
      (photonGaussianUnitary BF κ W a q, photonGaussianUnitary BF κ W b q) ∈
        (hardRadiationOperator κ).graph) hix hrx).mpr hpoint

set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
theorem gaussianReference_hard_graph (u : Reference (Fin N × Fin 3) V)
    (i : Fin N × Fin 3) :
    ∀ᵐ qx ∂W.space.measure.prod volume,
      (photonGaussianSource BF κ W N (inclusion (Fin N × Fin 3) V u) qx,
        photonGaussianSource BF κ W N
          (field (Fin N × Fin 3) V C (PhysicalRemovalKernels.hard F χ N κ)
            (PhysicalRemovalKernels.hard_measurable F χ N κ) (PhysicalRemovalKernels.bound F χ)
            (PhysicalRemovalKernels.hard_bound F χ N κ) i u) qx) ∈
        (hardFieldOperator κ (PhysicalRemovalKernels.hard F χ N κ i qx.2).val.1).graph := by
  have h := productSource_hard_field_graph (X := Configuration N) volume BF κ W C
    (PhysicalRemovalKernels.hard F χ N κ i) (PhysicalRemovalKernels.hard_measurable F χ N κ i)
    (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.hard_bound F χ N κ i)
    (ae_of_all _ (PhysicalRemovalKernels.hard_mem F χ N κ i))
    (radiationSource (Fin N × Fin 3) V u)
  exact (congrArg (fun v : WaveSpace (Fin N × Fin 3) =>
    ∀ᵐ qx ∂W.space.measure.prod (volume : Measure (Configuration N)),
      (photonGaussianSource BF κ W N v qx,
        photonGaussianSource BF κ W N
          (field (Fin N × Fin 3) V C (PhysicalRemovalKernels.hard F χ N κ)
            (PhysicalRemovalKernels.hard_measurable F χ N κ) (PhysicalRemovalKernels.bound F χ)
            (PhysicalRemovalKernels.hard_bound F χ N κ) i u) qx) ∈
        (hardFieldOperator κ (PhysicalRemovalKernels.hard F χ N κ i qx.2).val.1).graph)
    (radiation_matches (Fin N × Fin 3) V u)).mp h

set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
theorem gaussianReference_rest_graph (hV : StronglyMeasurable V)
    (u : Reference (Fin N × Fin 3) V) :
    ∀ᵐ qx ∂W.space.measure.prod volume,
      (photonGaussianSource BF κ W N (inclusion (Fin N × Fin 3) V u) qx,
        productSource (X := Configuration N) (Q := W.space.Q)
          (H := WithLp 2 (PhotonFock × PhotonFock))
          (K := WithLp 2 (HardPhotonFock κ × HardPhotonFock κ)) volume W.space.measure
          (productUnitary (H := PhotonFock) (K := HardPhotonFock κ)
            W.space.measure (photonGaussianUnitary BF κ W))
          (gaussianRestReference V C B BF κ W u) qx) ∈
        (hardRestOperator κ (Real.sqrt (V qx.2) : ℂ)).graph := by
  have hp : potential (Fin N × Fin 3) V u =ᵐ[volume]
      fun x => (Real.sqrt (V x) : ℂ) • inclusion (Fin N × Fin 3) V u x := by
    have h := (potentialSource (Fin N × Fin 3) V u).property
    change potential (Fin N × Fin 3) V u =ᵐ[volume]
      fun x => (Real.sqrt (V x) : ℂ) •
        PhysicalMultiplicationGraph.inclusion volume _ (potentialSource (Fin N × Fin 3) V u) x at h
    exact (congrArg (fun v : WaveSpace (Fin N × Fin 3) =>
      potential (Fin N × Fin 3) V u =ᵐ[volume]
        fun x => (Real.sqrt (V x) : ℂ) • v x)
      (potential_matches (Fin N × Fin 3) V u)).mp h
  have hscalar := productSource_scalar_unbounded (X := Configuration N) (Q := W.space.Q)
    (H := PhotonFock) (K := HardPhotonFock κ) volume W.space.measure
    (photonGaussianUnitary BF κ W) (fun x => (Real.sqrt (V x) : ℂ))
    (Complex.continuous_ofReal.comp_stronglyMeasurable
      (Real.continuous_sqrt.comp_stronglyMeasurable hV))
    (inclusion (Fin N × Fin 3) V u) (potential (Fin N × Fin 3) V u) hp
  have hpair := productSource_pair (X := Configuration N) (Q := W.space.Q)
    (H := PhotonFock) (K := HardPhotonFock κ) volume W.space.measure (photonGaussianUnitary BF κ W)
    (hardReference V C B BF κ W u) (potential (Fin N × Fin 3) V u)
  filter_upwards [gaussianReference_radiation_graph V F κ BF C W B u, hscalar, hpair]
    with qx hr hpq hpairq
  change (_, productSource (X := Configuration N) (Q := W.space.Q)
    (H := WithLp 2 (PhotonFock × PhotonFock))
    (K := WithLp 2 (HardPhotonFock κ × HardPhotonFock κ)) volume W.space.measure
    (productUnitary (H := PhotonFock) (K := HardPhotonFock κ)
      W.space.measure (photonGaussianUnitary BF κ W))
    (pairL2Isometry (H := PhotonFock) (K := PhotonFock) volume (WithLp.toLp 2
      (hardReference V C B BF κ W u, potential (Fin N × Fin 3) V u))) qx) ∈ _
  apply (congrArg (fun v : WithLp 2 (HardPhotonFock κ × HardPhotonFock κ) =>
    (photonGaussianSource BF κ W N (inclusion (Fin N × Fin 3) V u) qx, v) ∈
      (hardRestOperator κ (Real.sqrt (V qx.2) : ℂ)).graph) hpairq).mpr
  exact (hardRestOperator_graph_iff κ _ _ _).mpr
    ⟨(hardRadiationOperator_graph_iff κ _ _).mp hr, hpq⟩

variable (φ : SpatialWISField (μ := W.space.measure)
  (fun g : DerivativeLabel => W.firstChaos (realLabel F χ κ hκ g)) removalLabel)

set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
theorem gaussianReference_covariant (e : ℝ) (u : Reference (Fin N × Fin 3) V)
    (i : Fin N × Fin 3) :
    photonGaussianSource BF κ W N
      (covariant (Fin N × Fin 3) V C (PhysicalRemovalKernels.full F χ N)
        (PhysicalRemovalKernels.full_measurable F χ N) (PhysicalRemovalKernels.bound F χ)
        (PhysicalRemovalKernels.full_bound F χ N) e i u) =ᵐ[W.space.measure.prod volume]
      fun qx => -Complex.I •
        photonGaussianSource BF κ W N (ordinary (Fin N × Fin 3) V i u) qx -
        (e : ℂ) • photonGaussianSource BF κ W N
          (field (Fin N × Fin 3) V C (PhysicalRemovalKernels.hard F χ N κ)
            (PhysicalRemovalKernels.hard_measurable F χ N κ) (PhysicalRemovalKernels.bound F χ)
            (PhysicalRemovalKernels.hard_bound F χ N κ) i u) qx -
        ((e * particleSoftField F χ κ hκ W N φ i qx : ℝ) : ℂ) •
          photonGaussianSource BF κ W N (inclusion (Fin N × Fin 3) V u) qx := by
  let U := photonGaussianSource BF κ W N
  let d := U (ordinary (Fin N × Fin 3) V i u)
  let a := U (field (Fin N × Fin 3) V C (PhysicalRemovalKernels.hard F χ N κ)
    (PhysicalRemovalKernels.hard_measurable F χ N κ) (PhysicalRemovalKernels.bound F χ)
    (PhysicalRemovalKernels.hard_bound F χ N κ) i u)
  let s := U (field (Fin N × Fin 3) V C (PhysicalRemovalKernels.soft F χ N κ)
    (PhysicalRemovalKernels.soft_measurable F χ N κ) (PhysicalRemovalKernels.bound F χ)
    (PhysicalRemovalKernels.soft_bound F χ N κ) i u)
  have he := PhysicalPFVacuumEnergy.reference_covariant_split (Fin N × Fin 3) V C
    (PhysicalRemovalKernels.full F χ N) (PhysicalRemovalKernels.hard F χ N κ)
    (PhysicalRemovalKernels.soft F χ N κ)
    (PhysicalRemovalKernels.full_measurable F χ N)
    (PhysicalRemovalKernels.hard_measurable F χ N κ)
    (PhysicalRemovalKernels.soft_measurable F χ N κ)
    (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.bound F χ)
    (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.full_bound F χ N)
    (PhysicalRemovalKernels.hard_bound F χ N κ) (PhysicalRemovalKernels.soft_bound F χ N κ)
    (fun j => ae_of_all _ (PhysicalRemovalKernels.full_eq_hard_add_soft F χ N κ j)) u e i
  have hU := map_covariant_split U.toLinearEquiv.toLinearMap (e : ℂ) he
    (covariant_apply (Fin N × Fin 3) V C (PhysicalRemovalKernels.hard F χ N κ)
      (PhysicalRemovalKernels.hard_measurable F χ N κ) (PhysicalRemovalKernels.bound F χ)
      (PhysicalRemovalKernels.hard_bound F χ N κ) e i u)
  have hs := productSource_particle_soft F χ κ hκ BF C W N φ i
    (radiationSource (Fin N × Fin 3) V u)
  have hs' := (congrArg (fun v : WaveSpace (Fin N × Fin 3) =>
    s =ᵐ[W.space.measure.prod (volume : Measure (Configuration N))]
      fun qx => (particleSoftField F χ κ hκ W N φ i qx : ℂ) • U v qx)
    (radiation_matches (Fin N × Fin 3) V u)).mp hs
  refine (EventuallyEq.of_eq (congrArg
    (fun z : Lp (HardPhotonFock κ) 2
      (W.space.measure.prod (volume : Measure (Configuration N))) => ⇑z) hU)).trans ?_
  exact lp_covariant_of_soft (H := HardPhotonFock κ)
    (μ := W.space.measure.prod (volume : Measure (Configuration N))) d a s
    (U (inclusion (Fin N × Fin 3) V u)) e (particleSoftField F χ κ hκ W N φ i) hs'

variable {V B}
  {x : B.Trace (WaveSpace (Fin N × Fin 3))} (s : Source (Fin N × Fin 3) V B x)
  (S : StandardClosedFormBackground) (e : ℝ)
  (he : (normalEnergy (Fin N × Fin 3) V C (PhysicalRemovalKernels.full F χ N)
    (PhysicalRemovalKernels.full_measurable F χ N) (PhysicalRemovalKernels.bound F χ)
    (PhysicalRemovalKernels.full_bound F χ N) B S e).expectation x < ⊤)
  (hm : (B.realization (WaveSpace (Fin N × Fin 3))).rank.trace x = 1)

set_option backward.isDefEq.respectTransparency.types true in
/-- The source PF record is a derived value, with no operator-core or
physical representation matching hypothesis. -/
def Source.gaussianPFData (hV : StronglyMeasurable V) :
    (s.gaussianLattice C (PhysicalRemovalKernels.full F χ N)
      (PhysicalRemovalKernels.full_measurable F χ N) (PhysicalRemovalKernels.bound F χ)
      (PhysicalRemovalKernels.full_bound F χ N) S e BF κ W he hm).original.PFData
      (hardRadiationOperator κ)
      (fun i x => hardFieldOperator κ (PhysicalRemovalKernels.hard F χ N κ i x).val.1)
      (fun x => hardRestOperator κ (Real.sqrt (V x) : ℂ)) e
      (fun _ => particleSoftField F χ κ hκ W N φ) where
  derivative n i := photonGaussianSource BF κ W N (ordinary (Fin N × Fin 3) V i (s.vector n))
  radiation n := photonGaussianSource BF κ W N (hardReference V C B BF κ W (s.vector n))
  hardField n i := photonGaussianSource BF κ W N
    (field (Fin N × Fin 3) V C (PhysicalRemovalKernels.hard F χ N κ)
      (PhysicalRemovalKernels.hard_measurable F χ N κ) (PhysicalRemovalKernels.bound F χ)
      (PhysicalRemovalKernels.hard_bound F χ N κ) i (s.vector n))
  weak n := productSource_weak (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
    (I := Fin N × Fin 3) W.space.measure (photonGaussianUnitary BF κ W)
    (exists_hilbertBasis ℂ PhotonFock).choose_spec.choose (electronic (Fin N × Fin 3) V (s.vector n))
  radiation_graph n := gaussianReference_radiation_graph V F κ BF C W B (s.vector n)
  hard_graph n i := gaussianReference_hard_graph V F χ κ BF C W (s.vector n) i
  rest_graph n := gaussianReference_rest_graph V F κ BF C W B hV (s.vector n)
  covariant_eq n i := gaussianReference_covariant V F χ κ hκ BF C W φ e (s.vector n) i

end GptLean.PhysicalPFSource
