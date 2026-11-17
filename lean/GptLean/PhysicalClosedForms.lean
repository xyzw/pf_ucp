import GptLean.PhysicalNormalTrace
import GptLean.PositiveForm
import GptLean.PhotonLocalizationChannelMeasurement
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
The ordinary closed-form spectral theorem, isolated from all physical
parameters. Bounded positive approximants represent the squared norm of
any closed linear operator, with infinity outside its domain. The normal
trace realization then constructs the corresponding positive form and
its spectral-source identities on the same trace space.
-/

noncomputable section

namespace GptLean.PhysicalClosedForms

open PhotonLocalizationChannel RemovalState PhysicalNormalTrace
open scoped ENNReal InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Spectral approximation of an arbitrary closed nonnegative quadratic
form, including a possibly nondense form domain. -/
structure GraphApproximation (D : H →ₗ.[ℂ] K) where
  operator : ℕ → H →L[ℂ] H
  nonneg : ∀ n v, 0 ≤ (⟪v, operator n v⟫_ℂ).re
  monotone : ∀ v, Monotone (fun n => (⟪v, operator n v⟫_ℂ).re)
  graph_value : ∀ v w, (v, w) ∈ D.graph →
    (⨆ n, ENNReal.ofReal (⟪v, operator n v⟫_ℂ).re) = ENNReal.ofReal (‖w‖ ^ 2)
  finite_domain : ∀ v,
    (⨆ n, ENNReal.ofReal (⟪v, operator n v⟫_ℂ).re) < ⊤ ↔ v ∈ D.domain

/-- A universal operator-theory background. It has no particle number,
form factor, localization map, constraint or attainment conclusion. -/
structure StandardClosedFormBackground where
  resolve : ∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (D : H →ₗ.[ℂ] K), D.IsClosed → GraphApproximation D

variable [CompleteSpace H]

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T} {D : H →ₗ.[ℂ] K}
  (A : GraphApproximation D) (normal : NormalTraceData R) (F : NormalFunctionalData R)

def truncation (n : ℕ) : T →L[ℝ] ℝ :=
  Complex.reCLM.comp (((ContinuousLinearMap.apply ℂ ℂ (A.operator n)).restrictScalars ℝ).comp F.repr)

omit [CompleteSpace T] in
@[simp] theorem truncation_rankOne (n : ℕ) (v : H) :
    truncation A F n (R.rankOne v) = (⟪v, A.operator n v⟫_ℂ).re := by
  change (F.repr (R.rankOne v) _).re = _
  rw [F.rankOne]

def positiveForm : PositiveForm (positiveTrace normal F) where
  truncation := truncation A F
  nonneg n x hx := normal.observable_nonneg _
    (fun v => by rw [truncation_rankOne]; exact A.nonneg n v) hx
  monotone x hx n m hnm := by
    have h := normal.observable_nonneg (truncation A F m - truncation A F n)
      (fun v => by
        simp only [sub_apply, truncation_rankOne]
        exact sub_nonneg.mpr (A.monotone v hnm)) hx
    exact sub_nonneg.mp h

theorem positiveForm_graph (v : H) (w : K) (h : (v, w) ∈ D.graph) :
    (positiveForm A normal F).expectation (R.rankOne v) = ENNReal.ofReal (‖w‖ ^ 2) := by
  change (⨆ n, ENNReal.ofReal (truncation A F n (R.rankOne v))) = _
  simp only [truncation_rankOne]
  exact A.graph_value v w h

theorem positiveForm_finite_iff (v : H) :
    (positiveForm A normal F).expectation (R.rankOne v) < ⊤ ↔ v ∈ D.domain := by
  change (⨆ n, ENNReal.ofReal (truncation A F n (R.rankOne v))) < ⊤ ↔ _
  simp only [truncation_rankOne]
  exact A.finite_domain v

theorem positiveForm_source {v : ℕ → H} {x : T}
    (hv : HasSum (fun n => R.rankOne (v n)) x) :
    (positiveForm A normal F).expectation x =
      ∑' n, (positiveForm A normal F).expectation (R.rankOne (v n)) := by
  rw [← hv.tsum_eq]
  exact (positiveForm A normal F).expectation_tsum hv.summable (fun n => R.rankOne_positive (v n))

theorem positiveForm_source_graph {v : ℕ → H} {w : ℕ → K} {x : T}
    (hv : HasSum (fun n => R.rankOne (v n)) x)
    (hgraph : ∀ n, (v n, w n) ∈ D.graph) :
    (positiveForm A normal F).expectation x = ∑' n, ENNReal.ofReal (‖w n‖ ^ 2) := by
  rw [positiveForm_source A normal F hv]
  exact tsum_congr fun n => positiveForm_graph A normal F (v n) (w n) (hgraph n)

end GptLean.PhysicalClosedForms
