import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Abstract bounded chart maps and their L2 representatives. -/

noncomputable section
namespace PfHk.OrdinaryPolarSobolevChart

open MeasureTheory

def LpRepresents {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    (μ : Measure X) (u : Lp H 2 μ) (f : X → H) : Prop :=
  u =ᵐ[μ] f

theorem LpRepresents.ae {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    {μ : Measure X} {u : Lp H 2 μ} {f : X → H} (h : LpRepresents μ u f) : u =ᵐ[μ] f := h

theorem LpRepresents.memLp {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    {μ : Measure X} {u : Lp H 2 μ} {f : X → H} (h : LpRepresents μ u f) : MemLp f 2 μ :=
  (memLp_congr_ae h).mp (Lp.memLp u)

structure ChartData {Q X H R J T : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℂ Q] [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup R] [NormedSpace ℂ R]
    (μ : Measure X) (rawValue rawTime : Q → X → H)
    (rawGradient : J → Q → X → H) (rawRadiation : Q → X → R)
    (validTest : T → Prop) (supported : Q → Prop)
    (testValue testTime : T → X → H)
    (testGradient : J → T → X → H) (testRadiation : T → X → R) where
  value : Q →L[ℂ] Lp H 2 μ
  time : Q →L[ℂ] Lp H 2 μ
  gradient : J → Q →L[ℂ] Lp H 2 μ
  radiation : Q →L[ℂ] Lp R 2 μ
  value_ae : ∀ u : Q, LpRepresents μ (value u) (rawValue u)
  time_ae : ∀ u : Q, LpRepresents μ (time u) (rawTime u)
  gradient_ae : ∀ (j : J) (u : Q), LpRepresents μ (gradient j u) (rawGradient j u)
  radiation_ae : ∀ u : Q, LpRepresents μ (radiation u) (rawRadiation u)
  lift : ∀ v : T, validTest v → ∃ u : Q, supported u ∧
    LpRepresents μ (value u) (testValue v) ∧
    LpRepresents μ (time u) (testTime v) ∧
    (∀ j : J, LpRepresents μ (gradient j u) (testGradient j v)) ∧
    LpRepresents μ (radiation u) (testRadiation v)

structure ChartFamily (C : ℝ → ℝ → ℝ → Type*) (MeasureProperty : ℝ → ℝ → Prop) where
  chart : ∀ (c a b : ℝ), C c a b
  quasiMeasurePreserving : ∀ (a b : ℝ), MeasureProperty a b

end PfHk.OrdinaryPolarSobolevChart
