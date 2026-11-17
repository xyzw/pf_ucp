import GptLean.PhysicalFockSpatialField
import GptLean.RemovalGaussianLatticeSource

/-!
The electronic L² radiation domain is the range of the actual graph
inclusion. Every graph-bounded photon operator has a unique spatial value
on that domain. Bounded electronic multiplication preserves the domain and
commutes with every such photon operator.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory Filter ElectronicLocalization RemovalSource
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

theorem radiationInclusion_injective : Function.Injective radiationGraphInclusion := by
  intro u v h
  have hz : (u - v).val.1 = 0 := sub_eq_zero.mpr h
  have ho := radiationRoot.graph_fst_eq_zero_snd (u - v).property hz
  apply Subtype.ext
  exact Prod.ext h (sub_eq_zero.mp ho)

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

theorem spatialRadiation_injective : Function.Injective (spatialRadiationInclusion ν) := by
  intro u v h
  apply Lp.ext
  filter_upwards [radiationGraphInclusion.coeFn_compLpL u,
    radiationGraphInclusion.coeFn_compLpL v] with x hu hv
  apply radiationInclusion_injective
  have he := congrArg (fun w : SpatialPhotonSpace ν => w x) h
  exact hu.symm.trans (he.trans hv)

def spatialRadiationDomain (u : SpatialPhotonSpace ν) : Prop :=
  ∃ q : SpatialRadiationGraph ν, spatialRadiationInclusion ν q = u

def spatialRadiationSource (u : SpatialPhotonSpace ν) (h : spatialRadiationDomain ν u) :
    SpatialRadiationGraph ν := Classical.choose h

theorem spatialRadiationSource_value (u : SpatialPhotonSpace ν)
    (h : spatialRadiationDomain ν u) :
    spatialRadiationInclusion ν (spatialRadiationSource ν u h) = u :=
  Classical.choose_spec h

theorem spatialRadiationSource_unique (u : SpatialRadiationGraph ν)
    (h : spatialRadiationDomain ν (spatialRadiationInclusion ν u)) :
    spatialRadiationSource ν (spatialRadiationInclusion ν u) h = u :=
  spatialRadiation_injective ν (spatialRadiationSource_value ν _ h)

/-- The off-domain value is zero. Every identity below uses the actual domain. -/
def spatialGraphApply (L : RadiationGraphSpace →L[ℂ] PhotonFock)
    (u : SpatialPhotonSpace ν) : SpatialPhotonSpace ν := by
  classical
  exact if h : spatialRadiationDomain ν u then
    L.compLpL 2 ν (spatialRadiationSource ν u h) else 0

theorem spatialGraphApply_of_graph (L : RadiationGraphSpace →L[ℂ] PhotonFock)
    (u : SpatialRadiationGraph ν) :
    spatialGraphApply ν L (spatialRadiationInclusion ν u) = L.compLpL 2 ν u := by
  classical
  have h : spatialRadiationDomain ν (spatialRadiationInclusion ν u) := ⟨u, rfl⟩
  change (if h : spatialRadiationDomain ν (spatialRadiationInclusion ν u) then
    L.compLpL 2 ν (spatialRadiationSource ν (spatialRadiationInclusion ν u) h) else 0) = _
  exact (dite_eq_left h).trans
    (congrArg (L.compLpL 2 ν) (spatialRadiationSource_unique ν u h))

theorem spatialGraphApply_add (L M : RadiationGraphSpace →L[ℂ] PhotonFock)
    (u : SpatialPhotonSpace ν) :
    spatialGraphApply ν (L + M) u = spatialGraphApply ν L u + spatialGraphApply ν M u := by
  by_cases h : spatialRadiationDomain ν u
  · unfold spatialGraphApply
    simp only [dite_eq_left h, ContinuousLinearMap.add_compLpL, add_apply]
  · simp only [spatialGraphApply, dite_eq_right h, add_zero]

private theorem graphRealProduct_memLp
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (g : X → ℝ) (hg : AEStronglyMeasurable g ν)
    (M : ℝ) (hb : ∀ x, |g x| ≤ M) (u : Lp H 2 ν) :
    MemLp (fun x => (g x : ℂ) • u x) 2 ν := by
  apply ((Lp.memLp u).norm.const_mul M).mono'
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hg).smul (Lp.memLp u).1)
  filter_upwards with x
  change ‖(g x : ℂ) • u x‖ ≤ M * ‖u x‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

private def graphRealProduct
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (g : X → ℝ) (hg : AEStronglyMeasurable g ν)
    (M : ℝ) (hb : ∀ x, |g x| ≤ M) (u : Lp H 2 ν) : Lp H 2 ν :=
  (graphRealProduct_memLp ν g hg M hb u).toLp _

private theorem compLpL_boundedRealProduct [SFinite ν]
    {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (L : H →L[ℂ] K) (g : X → ℝ) (hg : AEStronglyMeasurable g ν)
    (M : ℝ) (hb : ∀ x, |g x| ≤ M) (u : Lp H 2 ν) :
    L.compLpL 2 ν (graphRealProduct ν g hg M hb u) =
      boundedRealProduct g hg M hb (L.compLpL 2 ν u) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (graphRealProduct ν g hg M hb u),
    L.coeFn_compLpL u,
    (graphRealProduct_memLp ν g hg M hb u).coeFn_toLp,
    (boundedRealProduct_memLp g hg M hb (L.compLpL 2 ν u)).coeFn_toLp]
    with x hL hu hgU hgL
  change graphRealProduct ν g hg M hb u x = (g x : ℂ) • u x at hgU
  change boundedRealProduct g hg M hb (L.compLpL 2 ν u) x =
    (g x : ℂ) • L.compLpL 2 ν u x at hgL
  rw [hL, hgU, hgL, hu]
  exact L.map_smul (g x : ℂ) (u x)

private theorem range_graph_locality [SFinite ν]
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (I L : G →L[ℂ] H) (D : Lp H 2 ν → Prop) (A : Lp H 2 ν → Lp H 2 ν)
    (hD : ∀ u, D u ↔ ∃ q : Lp G 2 ν, I.compLpL 2 ν q = u)
    (hA : ∀ q : Lp G 2 ν, A (I.compLpL 2 ν q) = L.compLpL 2 ν q) :
    SpatialRadiationLocality (H := H) (ν := ν) D A := by
  intro g hg M hb u hu
  obtain ⟨q, rfl⟩ := (hD u).mp hu
  have hin := compLpL_boundedRealProduct ν I g hg M hb q
  refine ⟨?_, ?_⟩
  · exact (hD _).mpr ⟨graphRealProduct ν g hg M hb q, hin⟩
  · rw [← hin, hA, hA]
    exact compLpL_boundedRealProduct ν L g hg M hb q

attribute [local irreducible] spatialRadiationDomain spatialGraphApply
  spatialRadiationInclusion radiationGraphInclusion

/-- Locality follows from pointwise graph inclusion and linearity. -/
theorem spatialGraphApply_locality [SFinite ν]
    (L : RadiationGraphSpace →L[ℂ] PhotonFock) :
    SpatialRadiationLocality (H := PhotonFock) (ν := ν)
      (spatialRadiationDomain ν) (spatialGraphApply ν L) := by
  apply range_graph_locality (G := RadiationGraphSpace) (H := PhotonFock)
    ν radiationGraphInclusion L
  · intro u
    unfold spatialRadiationDomain spatialRadiationInclusion
    rfl
  · intro q
    simpa only [spatialRadiationInclusion] using spatialGraphApply_of_graph ν L q

end GptLean.PhysicalFock
