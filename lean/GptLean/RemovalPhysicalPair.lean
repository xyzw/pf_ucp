import GptLean.RemovalConstraints
import GptLean.Gaussian.Disintegration

/-!
Physical density and current equality from the complete bounded spatial
test family. Universal trace formulas identify the physical L¹ functions.
Indicator tests then prove almost-everywhere equality, including all
current components on one common full-measure set.
-/

noncomputable section

namespace GptLean.RemovalConstraints

open MeasureTheory Filter RemovalState RemovalConstruction

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

structure BoundedSpatialTest (ν : Measure X) where
  weight : X → ℝ
  measurable : AEStronglyMeasurable weight ν
  bounded : ∀ x, ‖weight x‖ ≤ 1

theorem ae_eq_of_boundedSpatialTests {f g : X → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    (ht : ∀ t : BoundedSpatialTest ν,
      (∫ x, t.weight x * f x ∂ν) = ∫ x, t.weight x * g x ∂ν) : f =ᵐ[ν] g := by
  apply Gaussian.ae_eq_of_all_bounded_tests (fun _ : ℕ => ContinuousLinearMap.id ℝ ℝ)
    (fun _ _ h => h 0) (fun _ => hf) (fun _ => hg)
  intro _ w hw hb
  exact ht ⟨w, hw, hb⟩

variable {T DensityTest CurrentTest Particle Direction : Type*}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {Tr : PositiveTraceData T} {E : PositiveForm Tr}
  [Fintype Particle] [Fintype Direction]

/-- Standard physical observable descriptions, valid on every finite
energy state. The current test is summed over particle coordinates,
with the component direction fixed. No removal state occurs in a field. -/
structure PhysicalPairData
    (density : DensityTest → T →L[ℝ] ℝ) (current : CurrentTest → FormObservable E)
    (ν : Measure X) (Particle Direction : Type*) [Fintype Particle] [Fintype Direction] where
  rho : E.State → X → ℝ
  currentDensity : E.State → X → EuclideanSpace ℝ Direction
  rho_integrable : ∀ m, Integrable (rho m) ν
  current_integrable : ∀ m j, Integrable (fun x => currentDensity m x j) ν
  densityTest : BoundedSpatialTest ν → DensityTest
  currentTest : Particle → Direction → BoundedSpatialTest ν → CurrentTest
  density_eval : ∀ m t, density (densityTest t) m.val = ∫ x, t.weight x * rho m x ∂ν
  current_eval : ∀ m j t, (∑ i, (current (currentTest i j t)).value m.val) =
    ∫ x, t.weight x * currentDensity m x j ∂ν

namespace PhysicalPairData

variable {density : DensityTest → T →L[ℝ] ℝ} {current : CurrentTest → FormObservable E}
  (P : PhysicalPairData density current ν Particle Direction)

theorem equal_of_testedPair {m m' : E.State}
    (h : testedPair density current m'.val = testedPair density current m.val) :
    P.rho m' =ᵐ[ν] P.rho m ∧ P.currentDensity m' =ᵐ[ν] P.currentDensity m := by
  have hd : (fun t => density t m'.val) = (fun t => density t m.val) := congrArg Prod.fst h
  have hj : (fun t => (current t).value m'.val) = (fun t => (current t).value m.val) :=
    congrArg Prod.snd h
  constructor
  · apply ae_eq_of_boundedSpatialTests (P.rho_integrable m') (P.rho_integrable m)
    intro t
    rw [← P.density_eval, ← P.density_eval]
    exact congrFun hd (P.densityTest t)
  · have hcomponent (j : Direction) :
        (fun x => P.currentDensity m' x j) =ᵐ[ν] (fun x => P.currentDensity m x j) := by
      apply ae_eq_of_boundedSpatialTests (P.current_integrable m' j) (P.current_integrable m j)
      intro t
      rw [← P.current_eval, ← P.current_eval]
      exact Finset.sum_congr rfl (fun i _ => congrFun hj (P.currentTest i j t))
    filter_upwards [ae_all_iff.mpr hcomponent] with x hx
    exact PiLp.ext hx

/-- Every exact-removal output has the original physical L¹ density and
current, provided its tests are the universal physical spatial tests. -/
theorem localizedOutput_equal
    {Marginal : Type*} {m : E.State} {marginal : E.State → Marginal} {target : Marginal}
    {Esoft C e k L a b : ℝ}
    (out : SoftRemoval.LocalizedOutput (VectorData.model (testedPair density current)) m
      marginal target Esoft C e k L a b) :
    P.rho out.state =ᵐ[ν] P.rho m ∧ P.currentDensity out.state =ᵐ[ν] P.currentDensity m :=
  P.equal_of_testedPair out.pair_eq

end PhysicalPairData
end GptLean.RemovalConstraints
