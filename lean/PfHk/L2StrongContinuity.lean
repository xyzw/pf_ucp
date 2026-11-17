import PfHk.L2OperatorDerivative
import PfHk.StrongOperatorDerivative

noncomputable section
namespace PfHk.L2StrongContinuity
open MeasureTheory Filter
open scoped ENNReal Topology

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem of_deriv {f : ℝ → Lp E 2 μ} {df : Lp E 2 μ} {t : ℝ}
    (h : L2OperatorDerivative.HasL2DerivAt f df t) : ContinuousAt f t := h.continuousAt

theorem apply_complex {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {A : ℝ → D →L[ℂ] H} {q : ℝ → D} {t C : ℝ}
    (hA : ∀ v, ContinuousAt (fun s => A s v) t)
    (hb : ∀ᶠ s in 𝓝 t, ‖A s‖ ≤ C) (hq : ContinuousAt q t) :
    ContinuousAt (fun s => A s (q s)) t := by
  letI : NormedSpace ℝ D := NormedSpace.restrictScalars ℝ ℂ D
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  let B : ℝ → D →L[ℝ] H := fun s => (A s).restrictScalars ℝ
  have hb' : ∀ᶠ s in 𝓝 t, ‖B s‖ ≤ C := by
    simpa only [B, ContinuousLinearMap.norm_restrictScalars] using hb
  exact StrongOperatorDerivative.tendsto_apply (A := B) (A₀ := B t) hA hb' hq

end PfHk.L2StrongContinuity
