import GptLean.PhysicalGaussianSourceOperations

/-! Pointwise graph identities pass to the actual spatial Gaussian source. -/

noncomputable section

namespace GptLean.PhysicalGaussianCoordinates

open MeasureTheory Filter
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {X Q E H K : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  (ν : Measure X) (μ : Measure Q) [SFinite ν] [SFinite μ] [IsSeparable μ]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]
  (U : H ≃ₗᵢ[ℂ] Lp K 2 μ)

theorem productSource_graph (L R : E →L[ℂ] H) (a : Q → ℝ)
    (ha : StronglyMeasurable a)
    (h : ∀ v, U (L v) =ᵐ[μ] fun q => a q • U (R v) q) (u : Lp E 2 ν) :
    productSource ν μ U (L.compLpL 2 ν u) =ᵐ[μ.prod ν]
      fun qx => (a qx.1 : ℂ) • productSource ν μ U (R.compLpL 2 ν u) qx := by
  apply productSource_varying_multiplier ν μ U (fun qx => (a qx.1 : ℂ))
    (Complex.continuous_ofReal.comp_stronglyMeasurable (ha.comp_measurable measurable_fst))
  filter_upwards [L.coeFn_compLpL u, R.coeFn_compLpL u] with x hL hR
  rw [hL, hR]
  simpa only [Complex.coe_smul] using h (u x)

end GptLean.PhysicalGaussianCoordinates
