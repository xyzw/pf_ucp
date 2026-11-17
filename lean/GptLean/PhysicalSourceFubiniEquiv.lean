import GptLean.PhysicalSourceFubini
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
Surjectivity of the constructed L2 Fubini map. Indicator functions with
values in the inner L2 space have explicit product-space preimages.
Density of simple functions and the closed range of an isometry give the
full unitary identification, with the same representative formulas.
-/

noncomputable section

namespace GptLean.PhysicalSourceFubini

open MeasureTheory Filter Set Repair
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [IsSeparable ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

private def indicatorProduct (s : Set X) (c : Lp H 2 ν) (z : X × Y) : H :=
  s.indicator (fun _ => c z.2) z.1

omit [SFinite μ] [SFinite ν] [IsSeparable ν] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
private theorem indicatorProduct_memLp {s : Set X} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : Lp H 2 ν) :
    MemLp (indicatorProduct s c) 2 (μ.prod ν) := by
  have hm : StronglyMeasurable (indicatorProduct s c) :=
    ((Lp.stronglyMeasurable c).comp_measurable measurable_snd).indicator
      (hs.preimage measurable_fst)
  have hi : Integrable (s.indicator (fun _ : X => (1 : ℝ))) μ :=
    (integrable_indicator_iff hs).mpr (integrableOn_const (C := (1 : ℝ)) hμs)
  have hc : Integrable (fun y => ‖c y‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable c)).mp (Lp.memLp c)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (hi.mul_prod hc).congr
  exact ae_of_all _ fun z => by
    by_cases hz : z.1 ∈ s
    · simp [indicatorProduct, hz]
    · simp [indicatorProduct, hz]

omit [CompleteSpace H] in
private theorem indicator_mem_range {s : Set X} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : Lp H 2 ν) :
    indicatorConstLp 2 hs hμs c ∈ Set.range (curryIsometry (H := H) (μ := μ) (ν := ν)) := by
  let w := (indicatorProduct_memLp hs hμs c).toLp (indicatorProduct s c)
  refine ⟨w, ?_⟩
  apply Lp.ext
  filter_upwards [curry_ae w, section_represents_ae w,
    Measure.ae_ae_of_ae_prod (indicatorProduct_memLp hs hμs c).coeFn_toLp,
    (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := hμs) (c := c))]
    with x hx hsection hw hi
  change curry w x = indicatorConstLp 2 hs hμs c x
  rw [hx, hi]
  apply Lp.ext
  by_cases hxs : x ∈ s
  · filter_upwards [hsection, hw] with y hy hwy
    simpa only [Set.indicator_of_mem hxs, indicatorProduct] using hy.trans hwy
  · filter_upwards [hsection, hw, Lp.coeFn_zero H 2 ν] with y hy hwy hz
    simpa only [Set.indicator_of_notMem hxs, indicatorProduct, hz, Pi.zero_apply]
      using hy.trans hwy

/-- Every iterated L2 class is the image of an actual product-space class. -/
theorem curry_surjective :
    Function.Surjective (curryIsometry (H := H) (μ := μ) (ν := ν)) := by
  let U := curryIsometry (H := H) (μ := μ) (ν := ν)
  have hclosed : IsClosed (Set.range U) :=
    U.isometry.antilipschitzWith.isClosed_range U.isometry.uniformContinuous
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun u => u ∈ Set.range U)
  · intro c s hs hμs
    simpa only [Lp.simpleFunc.coe_indicatorConst] using indicator_mem_range hs hμs.ne c
  · intro f g hf hg _ hfr hgr
    rcases hfr with ⟨u, hu⟩
    rcases hgr with ⟨v, hv⟩
    exact ⟨u + v, by rw [map_add, hu, hv]⟩
  · exact hclosed

/-- The actual Fubini unitary used for conditional source sections. -/
def curryEquiv : ProductL2 (H := H) (μ := μ) (ν := ν) ≃ₗᵢ[ℂ]
    IteratedL2 (H := H) (μ := μ) (ν := ν) :=
  LinearIsometryEquiv.ofSurjective curryIsometry curry_surjective

@[simp] theorem curryEquiv_apply (u : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    curryEquiv u = curry u := rfl

theorem curryEquiv_represents_ae (u : ProductL2 (H := H) (μ := μ) (ν := ν)) :
    ∀ᵐ x ∂μ, (curryEquiv u x : Y → H) =ᵐ[ν] (fun y => u (x, y)) := by
  filter_upwards [curry_ae u, section_represents_ae u] with x hx hy
  simpa only [curryEquiv_apply, hx] using hy

end GptLean.PhysicalSourceFubini
