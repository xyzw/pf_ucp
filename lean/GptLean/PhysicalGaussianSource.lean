import GptLean.PhysicalGaussianCoordinates
import GptLean.RemovalSourceLatticeRepresentatives
import GptLean.RemovalSourceSymmetry

/-!
The constructed spatial Gaussian source commutes with electronic scalar
multiplication and measure-preserving electronic coordinate changes.
These are consequences of its fiberwise definition, not matching inputs.
-/

noncomputable section

namespace GptLean.PhysicalGaussianCoordinates

open MeasureTheory Filter Topology RemovalSource
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {X Q H K : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  (ν : Measure X) (μ : Measure Q) [SFinite μ] [SFinite ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K] [IsSeparable μ]

omit [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K] [IsSeparable μ] in
theorem ae_eq_of_swapped_sections {f g : Q × X → K}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (h : ∀ᵐ x ∂ν, ∀ᵐ q ∂μ, f (q, x) = g (q, x)) : f =ᵐ[μ.prod ν] g := by
  have hs : (fun xq : X × Q => f (xq.2, xq.1)) =ᵐ[ν.prod μ]
      fun xq => g (xq.2, xq.1) :=
    (Measure.ae_prod_iff_ae_ae
      ((hf.comp_measurable measurable_swap).measurableSet_eq_fun
        (hg.comp_measurable measurable_swap))).mpr h
  exact (Measure.measurePreserving_swap (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hs

variable (U : H ≃ₗᵢ[ℂ] Lp K 2 μ)

private theorem productSource_scalar_stronglyMeasurable
    (g : X → ℝ) (hg : StronglyMeasurable g) (u v : Lp H 2 ν)
    (h : (v : X → H) =ᵐ[ν] fun x => (g x : ℂ) • u x) :
    productSource ν μ U v =ᵐ[μ.prod ν]
      fun qx => (g qx.2 : ℂ) • productSource ν μ U u qx := by
  apply ae_eq_of_swapped_sections ν μ (Lp.stronglyMeasurable _)
    ((Complex.continuous_ofReal.comp_stronglyMeasurable
      (hg.comp_measurable measurable_snd)).smul (Lp.stronglyMeasurable _))
  filter_upwards [productSource_represents ν μ U u,
    productSource_represents ν μ U v, h] with x hu hv hx
  have he : U (v x) = (g x : ℂ) • U (u x) := by rw [hx, map_smul]
  filter_upwards [hu, hv, Lp.coeFn_smul (g x : ℂ) (U (u x))] with q huq hvq hq
  change productSource ν μ U v (q, x) = (g x : ℂ) • productSource ν μ U u (q, x)
  rw [hvq, he, hq, Pi.smul_apply, huq]

/-- The scalar intertwining required by lattice removal holds for the
constructed product-space source. -/
theorem productSource_scalar : SpatialScalarIntertwining (productSource ν μ U) := by
  intro g hg _ _ u v h
  let g' := hg.mk g
  have hg' : StronglyMeasurable g' := hg.stronglyMeasurable_mk
  have he : g =ᵐ[ν] g' := hg.ae_eq_mk
  have hv : (v : X → H) =ᵐ[ν] fun x => (g' x : ℂ) • u x := by
    filter_upwards [h, he] with x hx hgx
    simpa only [hgx] using hx
  have hp := productSource_scalar_stronglyMeasurable ν μ U g' hg' u v hv
  filter_upwards [hp, (Measure.quasiMeasurePreserving_snd (μ := μ)).ae he]
    with qx hqx hgx
  simpa only [hgx] using hqx

/-- Every measure-preserving change of electronic variables commutes with
the same source unitary. -/
theorem productSource_pullback (e : X → X) (he : MeasurePreserving e ν ν)
    (u v : Lp H 2 ν) (h : (u : X → H) =ᵐ[ν] fun x => v (e x)) :
    productSource ν μ U u =ᵐ[μ.prod ν]
      fun qx => productSource ν μ U v (qx.1, e qx.2) := by
  apply ae_eq_of_swapped_sections ν μ (Lp.stronglyMeasurable _)
    ((Lp.stronglyMeasurable _).comp_measurable
      (measurable_fst.prodMk (he.measurable.comp measurable_snd)))
  filter_upwards [productSource_represents ν μ U u,
    he.quasiMeasurePreserving.ae (productSource_represents ν μ U v), h]
    with x hu hv hx
  filter_upwards [hu, hv] with q huq hvq
  change productSource ν μ U u (q, x) = productSource ν μ U v (q, e x)
  rw [huq, hvq, hx]

/-- Bounded photon operator intertwining passes to the same spatial source. -/
theorem productSource_fiberOperator (A : H →L[ℂ] H) (D : K →L[ℂ] K)
    (h : ∀ v, U (A v) = D.compLpL 2 μ (U v)) (u : Lp H 2 ν) :
    productSource ν μ U (A.compLpL 2 ν u) =
      D.compLpL 2 (μ.prod ν) (productSource ν μ U u) := by
  apply Lp.ext
  apply ae_eq_of_swapped_sections ν μ (Lp.stronglyMeasurable _) (Lp.stronglyMeasurable _)
  have hD := (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae
    (D.coeFn_compLpL (productSource ν μ U u))
  filter_upwards [productSource_represents ν μ U u,
    productSource_represents ν μ U (A.compLpL 2 ν u), A.coeFn_compLpL u,
    Measure.ae_ae_of_ae_prod hD] with x hu hv hx hdx
  have he : U (A.compLpL 2 ν u x) = D.compLpL 2 μ (U (u x)) := by rw [hx, h]
  filter_upwards [hu, hv, hdx, D.coeFn_compLpL (U (u x))] with q huq hvq hdq heq
  change D.compLpL 2 (μ.prod ν) (productSource ν μ U u) (q, x) =
    D (productSource ν μ U u (q, x)) at hdq
  rw [hvq, he, heq, hdq, huq]

/-- A fiber multiplication identity passes through the actual product
source and Fubini to the electronic L² fibers. -/
theorem spatialUnitary_intertwining [IsSeparable ν]
    (a : Q → ℝ) (ha : StronglyMeasurable a) (u v : Lp H 2 ν)
    (h : ∀ᵐ x ∂ν, U (v x) =ᵐ[μ] fun q => a q • U (u x) q) :
    spatialUnitary ν μ U v =ᵐ[μ] fun q => a q • spatialUnitary ν μ U u q := by
  have hp : productSource ν μ U v =ᵐ[μ.prod ν]
      fun qx => a qx.1 • productSource ν μ U u qx := by
    apply ae_eq_of_swapped_sections ν μ (Lp.stronglyMeasurable _)
      ((ha.comp_measurable measurable_fst).smul (Lp.stronglyMeasurable _))
    filter_upwards [productSource_represents ν μ U u,
      productSource_represents ν μ U v, h] with x hu hv hx
    filter_upwards [hu, hv, hx] with q huq hvq hq
    change productSource ν μ U v (q, x) = a q • productSource ν μ U u (q, x)
    rw [hvq, hq, huq]
  filter_upwards [PhysicalSourceFubini.curryEquiv_represents_ae (productSource ν μ U u),
    PhysicalSourceFubini.curryEquiv_represents_ae (productSource ν μ U v),
    Measure.ae_ae_of_ae_prod hp] with q hu hv hq
  apply Lp.ext
  filter_upwards [hu, hv, hq,
    Lp.coeFn_smul (a q) (spatialUnitary ν μ U u q)] with x hux hvx hqx hs
  exact hvx.trans (hqx.trans ((congrArg (a q • ·) hux.symm).trans hs.symm))

end GptLean.PhysicalGaussianCoordinates
