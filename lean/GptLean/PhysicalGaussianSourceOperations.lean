import GptLean.PhysicalGaussianSource
import GptLean.PhysicalGaussianProduct

/-!
Scalar multiplication and Hilbert pairs for the actual Gaussian source.
No boundedness of the scalar is needed when both vectors already belong
to L². This includes the potential term of the reference form.
-/

noncomputable section
namespace GptLean.PhysicalGaussianCoordinates

open MeasureTheory Filter
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {X Q H K : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  (ν : Measure X) (μ : Measure Q) [SFinite ν] [SFinite μ] [IsSeparable μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]
  (U : H ≃ₗᵢ[ℂ] Lp K 2 μ)

theorem productSource_varying_multiplier (a : Q × X → ℂ)
    (ha : StronglyMeasurable a) (u v : Lp H 2 ν)
    (h : ∀ᵐ x ∂ν, U (v x) =ᵐ[μ] fun q => a (q, x) • U (u x) q) :
    productSource ν μ U v =ᵐ[μ.prod ν]
      fun qx => a qx • productSource ν μ U u qx := by
  apply ae_eq_of_swapped_sections ν μ (Lp.stronglyMeasurable _)
    (ha.smul (Lp.stronglyMeasurable _))
  filter_upwards [productSource_represents ν μ U u,
    productSource_represents ν μ U v, h] with x hu hv hx
  filter_upwards [hu, hv, hx] with q huq hvq hq
  change productSource ν μ U v (q, x) = a (q, x) • productSource ν μ U u (q, x)
  rw [hvq, hq, huq]

theorem productSource_scalar_unbounded (a : X → ℂ) (ha : StronglyMeasurable a)
    (u v : Lp H 2 ν) (h : v =ᵐ[ν] fun x => a x • u x) :
    productSource ν μ U v =ᵐ[μ.prod ν]
      fun qx => a qx.2 • productSource ν μ U u qx := by
  apply productSource_varying_multiplier ν μ U (fun qx => a qx.2)
    (ha.comp_measurable measurable_snd) u v
  filter_upwards [h] with x hx
  have he : U (v x) = a x • U (u x) := by rw [hx, map_smul]
  exact (EventuallyEq.of_eq (congrArg (fun f : Lp K 2 μ => ⇑f) he)).trans
    (Lp.coeFn_smul (a x) (U (u x)))

theorem productSource_pair (u v : Lp H 2 ν) :
    productSource ν μ (productUnitary μ U)
      (pairL2Isometry ν (WithLp.toLp 2 (u, v))) =ᵐ[μ.prod ν]
      fun qx => WithLp.toLp 2
        (productSource ν μ U u qx, productSource ν μ U v qx) := by
  apply ae_eq_of_swapped_sections ν μ (Lp.stronglyMeasurable _)
    ((WithLp.prodContinuousLinearEquiv 2 ℂ K K).symm.continuous.comp_stronglyMeasurable
      ((Lp.stronglyMeasurable _).prodMk (Lp.stronglyMeasurable _)))
  filter_upwards [productSource_represents ν μ U u,
    productSource_represents ν μ U v,
    productSource_represents ν μ (productUnitary μ U)
      (pairL2Isometry ν (WithLp.toLp 2 (u, v))),
    pairL2Linear_ae ν (WithLp.toLp 2 (u, v))] with x hu hv hp hx
  have hp' := productUnitary_ae μ U (WithLp.toLp 2 (u x, v x))
  filter_upwards [hu, hv, hp, hp'] with q huq hvq hpq hpair
  rw [hpq]
  change productUnitary μ U (pairL2Linear ν (WithLp.toLp 2 (u, v)) x) q = _
  rw [hx]
  change productUnitary μ U (WithLp.toLp 2 (u x, v x)) q =
    WithLp.toLp 2 (productSource ν μ U u (q, x), productSource ν μ U v (q, x))
  rw [hpair]
  change WithLp.toLp 2 (U (u x) q, U (v x) q) = _
  rw [huq, hvq]

end GptLean.PhysicalGaussianCoordinates
