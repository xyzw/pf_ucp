import GptLean.PhysicalClosedForms
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
Normal quadratic forms on an injective complete graph domain. Appending
any bounded graph-domain operator preserves the coercive graph estimate.
Polarization can therefore compare source ensembles without postulating
decomposition independence of an unbounded observable.
-/

noncomputable section

namespace GptLean.PhysicalGraphForms

open PhysicalClosedForms PhysicalNormalTrace
open scoped ENNReal NNReal InnerProductSpace

variable (E H K : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

structure CoerciveGraph where
  value : E →L[ℂ] H
  output : E →L[ℂ] K
  injective : Function.Injective value
  constant : ℝ≥0
  bound : ∀ u, ‖u‖ ≤ constant * ‖(value u, output u)‖

namespace CoerciveGraph

variable {E H K} [CompleteSpace E]
  (G : CoerciveGraph E H K)

def graphMap : E →L[ℂ] H × K := G.value.prod G.output

theorem graphMap_closed : IsClosed (Set.range G.graphMap) :=
  (G.graphMap.antilipschitz_of_bound (K := G.constant) G.bound).isClosed_range
    G.graphMap.uniformContinuous

def graph : Submodule ℂ (H × K) := G.graphMap.range

omit [CompleteSpace E] in
private theorem graph_fst_zero (z : H × K) (hz : z ∈ G.graph) (h : z.1 = 0) :
    z.2 = 0 := by
  obtain ⟨u, hu⟩ := hz
  have hv : G.value u = 0 := (congrArg Prod.fst hu).trans h
  have hu0 : u = 0 := G.injective (hv.trans (map_zero _).symm)
  rw [hu0, map_zero] at hu
  exact (congrArg Prod.snd hu).symm

def operator : H →ₗ.[ℂ] K := G.graph.toLinearPMap

omit [CompleteSpace E] in
theorem operator_graph : G.operator.graph = G.graph :=
  Submodule.toLinearPMap_graph_eq _ G.graph_fst_zero

theorem operator_closed : G.operator.IsClosed := by
  change IsClosed (G.operator.graph : Set (H × K))
  rw [G.operator_graph]
  exact G.graphMap_closed

omit [CompleteSpace E] in
theorem mem_operator (u : E) : (G.value u, G.output u) ∈ G.operator.graph := by
  rw [G.operator_graph]
  exact ⟨u, rfl⟩

variable [CompleteSpace H] [CompleteSpace K]
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

def normalForm : RemovalState.PositiveForm (B.traceData (H := H)) :=
  positiveForm (S.resolve H K G.operator G.operator_closed)
    B.normal (B.realization H).functional

theorem normalForm_rankOne (u : E) :
    (G.normalForm B S).expectation ((B.realization H).rank.rankOne (G.value u)) =
      ENNReal.ofReal (‖G.output u‖ ^ 2) :=
  positiveForm_graph _ _ _ _ _ (G.mem_operator u)

theorem normalForm_source {u : ℕ → E} {x : B.Trace H}
    (hu : HasSum (fun n => (B.realization H).rank.rankOne (G.value (u n))) x) :
    (G.normalForm B S).expectation x = ∑' n, ENNReal.ofReal (‖G.output (u n)‖ ^ 2) := by
  exact positiveForm_source_graph _ _ _ hu (fun n => G.mem_operator (u n))

theorem normalForm_source_hasSum {u : ℕ → E} {x : B.Trace H}
    (hu : HasSum (fun n => (B.realization H).rank.rankOne (G.value (u n))) x)
    (hs : Summable (fun n => ‖G.output (u n)‖ ^ 2)) :
    HasSum (fun n => ‖G.output (u n)‖ ^ 2) ((G.normalForm B S).expectation x).toReal := by
  rw [G.normalForm_source B S hu, ← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hs,
    ENNReal.toReal_ofReal (tsum_nonneg fun n => sq_nonneg _)]
  exact hs.hasSum

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def appendOutput (L : E →L[ℂ] F) : E →L[ℂ] WithLp 2 (K × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ K F).symm.toContinuousLinearMap.comp (G.output.prod L)

omit [CompleteSpace E] [CompleteSpace H] [CompleteSpace K] in
theorem appendOutput_norm_sq (L : E →L[ℂ] F) (u : E) :
    ‖G.appendOutput L u‖ ^ 2 = ‖G.output u‖ ^ 2 + ‖L u‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

def append (L : E →L[ℂ] F) : CoerciveGraph E H (WithLp 2 (K × F)) where
  value := G.value
  output := G.appendOutput L
  injective := G.injective
  constant := G.constant
  bound u := by
    apply (G.bound u).trans
    apply mul_le_mul_of_nonneg_left _ G.constant.coe_nonneg
    change max ‖G.value u‖ ‖G.output u‖ ≤ max ‖G.value u‖ ‖G.appendOutput L u‖
    apply max_le_max_left
    have h := G.appendOutput_norm_sq L u
    nlinarith [sq_nonneg ‖L u‖, norm_nonneg (G.output u), norm_nonneg (G.appendOutput L u)]

end CoerciveGraph

end GptLean.PhysicalGraphForms
