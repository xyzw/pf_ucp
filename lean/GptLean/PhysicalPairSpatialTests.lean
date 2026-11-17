import GptLean.PhysicalPairTests
import GptLean.PhysicalPairDuality

/-! Continuous linear versions of the separating scalar spatial tests. -/

noncomputable section

namespace GptLean.PhysicalPairSpace

open MeasureTheory RemovalConstraints PhysicalPairDuality
open scoped ENNReal

abbrev SpatialTest := BoundedSpatialTest (volume : Measure Position)

def spatialTestLp (t : SpatialTest) : Lp ℝ ∞ (volume : Measure Position) :=
  (memLp_top_of_bound t.measurable 1 (ae_of_all _ t.bounded)).toLp t.weight

theorem spatialTestLp_ae (t : SpatialTest) :
    (spatialTestLp t : Position → ℝ) =ᵐ[volume] t.weight :=
  (memLp_top_of_bound t.measurable 1 (ae_of_all _ t.bounded)).coeFn_toLp

def spatialDensityTest (t : SpatialTest) : Pair →L[ℝ] ℝ :=
  (lpInner (spatialTestLp t)).comp densityL1

def currentComponent (b : Fin 3) : Pair →L[ℝ] Lp ℝ 1 (volume : Measure Position) :=
  ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) b).compLpL 1 volume).comp currentL1

def spatialCurrentTest (b : Fin 3) (t : SpatialTest) : Pair →L[ℝ] ℝ :=
  (lpInner (spatialTestLp t)).comp (currentComponent b)

theorem spatialDensityTest_eq (t : SpatialTest) (p : Pair) :
    spatialDensityTest t p = ∫ x, t.weight x * densityL1 p x := by
  change lpInner (spatialTestLp t) (densityL1 p) = _
  rw [lpInner_eq_integral]
  apply integral_congr_ae
  filter_upwards [spatialTestLp_ae t] with x hx
  simp only [hx, Real.inner_apply]

theorem spatialCurrentTest_eq (b : Fin 3) (t : SpatialTest) (p : Pair) :
    spatialCurrentTest b t p = ∫ x, t.weight x * currentL1 p x b := by
  change lpInner (spatialTestLp t) (currentComponent b p) = _
  rw [lpInner_eq_integral]
  apply integral_congr_ae
  filter_upwards [spatialTestLp_ae t,
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) b).coeFn_compLpL (currentL1 p)] with x hx hy
  change inner ℝ (spatialTestLp t x)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) b).compLpL 1 volume (currentL1 p) x) = _
  rw [hx, hy]
  simp only [PiLp.proj_apply, Real.inner_apply]

theorem pair_eq_of_spatial_test_maps (p q : Pair)
    (hρ : ∀ t, spatialDensityTest t p = spatialDensityTest t q)
    (hj : ∀ b t, spatialCurrentTest b t p = spatialCurrentTest b t q) : p = q := by
  apply pair_eq_of_bounded_spatial_tests
  · intro t
    exact (spatialDensityTest_eq t p).symm.trans ((hρ t).trans (spatialDensityTest_eq t q))
  · intro b t
    exact (spatialCurrentTest_eq b t p).symm.trans ((hj b t).trans (spatialCurrentTest_eq b t q))

end GptLean.PhysicalPairSpace
