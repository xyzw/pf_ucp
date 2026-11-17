import GptLean.PhysicalPairSpace
import Mathlib.Analysis.Normed.Operator.Banach

/-!
A linear source with proved membership in a second Lp space has a bounded
map into that space. Closedness follows from uniqueness of convergence in
measure. This uses the ordinary Banach closed-graph theorem and no bound
or convergence assumption on the output map.
-/

noncomputable section

namespace GptLean.PhysicalLpUpgrade

open MeasureTheory Filter Topology
open scoped ENNReal

variable {X Q H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  (L : Q →L[ℝ] Lp H p μ) (hm : ∀ u, MemLp (L u) q μ)

def linear : Q →ₗ[ℝ] Lp H q μ where
  toFun u := (hm u).toLp (L u)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(hm (u + v)).coeFn_toLp, (hm u).coeFn_toLp,
      (hm v).coeFn_toLp, Lp.coeFn_add ((hm u).toLp (L u)) ((hm v).toLp (L v)),
      Lp.coeFn_add (L u) (L v)] with x huv hu hv hsum hL
    have he := congrArg (fun f : Lp H p μ => f x) (L.map_add u v)
    exact huv.trans (he.trans (hL.trans ((congrArg₂ (· + ·) hu hv).symm.trans hsum.symm)))
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(hm (c • u)).coeFn_toLp, (hm u).coeFn_toLp,
      Lp.coeFn_smul c ((hm u).toLp (L u)), Lp.coeFn_smul c (L u)]
      with x hcu hu hsm hL
    have he := congrArg (fun f : Lp H p μ => f x) (L.map_smul c u)
    exact hcu.trans (he.trans (hL.trans ((congrArg (c • ·) hu).symm.trans hsm.symm)))

omit [CompleteSpace Q] [CompleteSpace H] [Fact (1 ≤ q)] in
theorem linear_ae (u : Q) : (linear L hm u : X → H) =ᵐ[μ] L u :=
  (hm u).coeFn_toLp

theorem linear_continuous : Continuous (linear L hm) := by
  apply (linear L hm).continuous_of_seq_closed_graph
  intro u a v hu hv
  have hp := tendstoInMeasure_of_tendsto_Lp ((L.continuous.tendsto a).comp hu)
  have hq := tendstoInMeasure_of_tendsto_Lp hv
  apply Lp.ext
  exact (tendstoInMeasure_ae_unique hq
    (hp.congr_left (fun n => (linear_ae L hm (u n)).symm))).trans
      (linear_ae L hm a).symm

def map : Q →L[ℝ] Lp H q μ :=
  ⟨linear L hm, linear_continuous L hm⟩

theorem map_ae (u : Q) : (map L hm u : X → H) =ᵐ[μ] L u :=
  linear_ae L hm u

end GptLean.PhysicalLpUpgrade
