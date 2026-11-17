import GptLean.PhysicalGaussianSource
import GptLean.PhysicalFockFieldGraphMeasurable
import GptLean.PhysicalFockHardGaussianGraph
import GptLean.PhysicalFockSpatialField

/-!
Actual position-dependent hard fields pass to the product Gaussian source.
Joint closedness of the Segal graph justifies Fubini for the spatially
varying kernel. The graph identity is derived from the concrete Fock split.
-/

noncomputable section
namespace GptLean.PhysicalGaussianCoordinates

open MeasureTheory Filter Topology
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section Relation

variable {X Q H H' K K' : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  (ν : Measure X) (μ : Measure Q) [SFinite ν] [SFinite μ] [IsSeparable μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  [TopologicalSpace.SeparableSpace K']
  (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (V : H' ≃ₗᵢ[ℂ] Lp K' 2 μ)

/-- A closed fiber relation passes through the actual spatial representatives. -/
theorem productSource_closed_relation (s : Set (K × K')) (hs : IsClosed s)
    (u : Lp H 2 ν) (v : Lp H' 2 ν)
    (h : ∀ᵐ x ∂ν, ∀ᵐ q ∂μ, (U (u x) q, V (v x) q) ∈ s) :
    ∀ᵐ qx ∂μ.prod ν, (productSource ν μ U u qx, productSource ν μ V v qx) ∈ s := by
  let : MeasurableSpace (K × K') := borel _
  have : BorelSpace (K × K') := ⟨rfl⟩
  have hm : MeasurableSet {xq : X × Q |
      (productSource ν μ U u (xq.2, xq.1), productSource ν μ V v (xq.2, xq.1)) ∈ s} :=
    hs.measurableSet.preimage
      (((Lp.stronglyMeasurable _).comp_measurable measurable_swap).prodMk
        ((Lp.stronglyMeasurable _).comp_measurable measurable_swap)).measurable
  have hh : ∀ᵐ x ∂ν, ∀ᵐ q ∂μ,
      (productSource ν μ U u (q, x), productSource ν μ V v (q, x)) ∈ s := by
    filter_upwards [productSource_represents ν μ U u,
      productSource_represents ν μ V v, h] with x hu hv hx
    filter_upwards [hu, hv, hx] with q huq hvq hq
    rwa [huq, hvq]
  exact (Measure.measurePreserving_swap (μ := μ) (ν := ν)).quasiMeasurePreserving.ae
    ((Measure.ae_prod_iff_ae_ae hm).mpr hh)

end Relation
end GptLean.PhysicalGaussianCoordinates

namespace GptLean.PhysicalFock

open MeasureTheory Filter PhysicalGaussianCoordinates
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] photonGaussianUnitary productSource

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [SFinite ν]
  (BF : StandardSymmetricFockExponential) (κ : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)
  (C : CanonicalSectorCCR photonMeasure)
  (k : X → WeightedPhotonKernel) (hk : AEStronglyMeasurable k ν)
  (M : ℝ) (hb : ∀ᵐ x ∂ν, ‖k x‖ ≤ M)

-- Match the normed-space parents used in the concrete Gaussian unitary.
local instance spatialGraphPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance spatialGraphHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

set_option backward.isDefEq.respectTransparency.types true in
/-- Spatial hard-field matching follows from the actual pointwise Fock theorem. -/
theorem productSource_hard_field_graph
    (hkhard : ∀ᵐ x ∂ν, (k x).val.1 ∈ hardOnePhoton κ) (u : SpatialRadiationGraph ν) :
    ∀ᵐ qx ∂W.space.measure.prod ν,
      (productSource (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
          ν W.space.measure (photonGaussianUnitary BF κ W)
          (spatialRadiationInclusion ν u) qx,
        productSource (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
          ν W.space.measure (photonGaussianUnitary BF κ W)
          (spatialField ν C k hk M hb u) qx) ∈ (hardFieldOperator κ (k qx.2).val.1).graph := by
  let U : PhotonFock ≃ₗᵢ[ℂ] Lp (HardPhotonFock κ) 2 W.space.measure := photonGaussianUnitary BF κ W
  let f : Lp (HardPhotonFock κ) 2 (W.space.measure.prod ν) :=
    productSource (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
      ν W.space.measure U (spatialRadiationInclusion ν u)
  let g : Lp (HardPhotonFock κ) 2 (W.space.measure.prod ν) :=
    productSource (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
      ν W.space.measure U (spatialField ν C k hk M hb u)
  have hk' : AEStronglyMeasurable (fun xq : X × W.space.Q => (k xq.1).val.1)
      (ν.prod W.space.measure) :=
    ((continuous_fst.comp continuous_subtype_val).comp_aestronglyMeasurable hk).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst
  have hf : AEStronglyMeasurable (fun xq : X × W.space.Q => (f (xq.2, xq.1)).val)
      (ν.prod W.space.measure) :=
    continuous_subtype_val.comp_aestronglyMeasurable
      ((Lp.stronglyMeasurable f).comp_measurable measurable_swap).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun xq : X × W.space.Q => (g (xq.2, xq.1)).val)
      (ν.prod W.space.measure) :=
    continuous_subtype_val.comp_aestronglyMeasurable
      ((Lp.stronglyMeasurable g).comp_measurable measurable_swap).aestronglyMeasurable
  have hm := segalGraph_nullMeasurableSet photonMeasure hk' hf hg
  have hh : ∀ᵐ x ∂ν, ∀ᵐ q ∂W.space.measure,
      SegalGraph photonMeasure (k x).val.1 (f (q, x)).val (g (q, x)).val := by
    filter_upwards [productSource_represents ν W.space.measure U (spatialRadiationInclusion ν u),
      productSource_represents ν W.space.measure U (spatialField ν C k hk M hb u),
      radiationGraphInclusion.coeFn_compLpL u, spatialField_ae ν C k hk M hb u, hkhard]
      with x hf hg hi hkx hsupport
    have hpoint := photonGaussianUnitary_hard_field_graph κ BF C W (k x) hsupport (u x)
    filter_upwards [hf, hg, hpoint] with q hfu hgu hq
    have hf' := hfu.trans (congrArg (fun a : PhotonFock => U a q) hi)
    have hg' := hgu.trans (congrArg (fun a : PhotonFock => U a q) hkx)
    exact (congrArg₂ (fun a b : HardPhotonFock κ =>
      SegalGraph photonMeasure (k x).val.1 a.val b.val) hf' hg').mpr
      ((hardFieldOperator_graph_iff κ (k x).val.1 _ _).mp hq)
  have hprod := (Measure.measurePreserving_swap (μ := W.space.measure) (ν := ν)).quasiMeasurePreserving.ae
    ((ae_prod_iff_ae_ae₀ hm).mpr hh)
  filter_upwards [hprod] with qx hqx
  exact (hardFieldOperator_graph_iff κ (k qx.2).val.1 _ _).mpr hqx

end GptLean.PhysicalFock
