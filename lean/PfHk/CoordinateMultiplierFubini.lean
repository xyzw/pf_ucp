import GptLean.TransformationsGaugeWeakSources

/-! A one-coordinate scalar multiplier has the same squared norm before
and after the actual Hilbert-valued Fubini isometry. -/

noncomputable section
namespace PfHk.CoordinateMultiplierFubini

open MeasureTheory GptLean GptLean.PhysicalSourceFubini
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 20000

variable {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [IsSeparable ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H]

theorem multiplier_norm_sq (u : ProductL2 (H := H) (μ := μ) (ν := ν))
    (b : X → ℝ)
    (hp : MemLp (fun p : X × Y => b p.1 • u p) 2 (μ.prod ν))
    (hm : MemLp (fun x => b x • curry u x) 2 μ) :
    ‖hp.toLp (fun p : X × Y => b p.1 • u p)‖ ^ 2 =
      ‖hm.toLp (fun x => b x • curry u x)‖ ^ 2 := by
  rw [Repair.toL2_norm_sq hp, Repair.toL2_norm_sq hm,
    integral_prod _ (hp.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))]
  apply integral_congr_ae
  filter_upwards [curry_norm_sq_ae u] with x hx
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, integral_const_mul]
  rw [hx]

theorem product_multiplier (u : ProductL2 (H := H) (μ := μ) (ν := ν))
    (b : X → ℝ) (hb : AEStronglyMeasurable b μ)
    (hm : MemLp (fun x => b x • curry u x) 2 μ) :
    ∃ hp : MemLp (fun p : X × Y => b p.1 • u p) 2 (μ.prod ν),
      ‖hp.toLp (fun p : X × Y => b p.1 • u p)‖ ^ 2 =
        ‖hm.toLp (fun x => b x • curry u x)‖ ^ 2 :=
  ⟨TransformationsGauge.memLp_smul_of_curry u hb hm,
    multiplier_norm_sq u b _ hm⟩

end PfHk.CoordinateMultiplierFubini
