import GptLean.RepresentabilityDensityMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-!
The ordinary scalar Hardy inequality in three dimensions is kept as
explicit universal analysis background. Integrating it over a finite
measure of centers is proved here. The background contains no electronic
configuration, density, photon state or representability conclusion.
-/

noncomputable section
set_option Elab.async false

namespace GptLean.Representability

open MeasureTheory SymmetricLift
open scoped ENNReal

/-- The translated three-dimensional Hardy inequality for scalar H1.
This is a universal analytic premise, not an axiom declaration. -/
structure StandardScalarHardy : Prop where
  estimate : ∀ (b : DisplacementPosition → ℝ)
    (db : Fin 3 → DisplacementPosition → ℝ),
    HasWeakH1Local b db → MemLp b 2 volume →
    (∀ i, MemLp (db i) 2 volume) → ∀ y : DisplacementPosition,
      Integrable (fun x => (‖x - y‖ ^ 2)⁻¹ * ‖b x‖ ^ 2) volume ∧
      (∫ x, (‖x - y‖ ^ 2)⁻¹ * ‖b x‖ ^ 2) ≤
        4 * ∑ i : Fin 3, (eLpNorm (db i) 2 volume).toReal ^ 2

namespace StandardScalarHardy

variable (Hardy : StandardScalarHardy)

include Hardy in
/-- Integrating the scalar inequality over any finite distribution of
centers preserves the same derivative constant times its total mass. -/
theorem product_estimate
    (b : DisplacementPosition → ℝ) (db : Fin 3 → DisplacementPosition → ℝ)
    (hb : HasWeakH1Local b db) (hb₂ : MemLp b 2 volume)
    (hdb₂ : ∀ i, MemLp (db i) 2 volume)
    (ν : Measure DisplacementPosition) [IsFiniteMeasure ν] :
    Integrable (fun p : DisplacementPosition × DisplacementPosition =>
      (‖p.2 - p.1‖ ^ 2)⁻¹ * ‖b p.2‖ ^ 2) (ν.prod volume) ∧
    (∫ p : DisplacementPosition × DisplacementPosition,
      (‖p.2 - p.1‖ ^ 2)⁻¹ * ‖b p.2‖ ^ 2 ∂ν.prod volume) ≤
      (measureUnivNNReal ν : ℝ) *
        (4 * ∑ i : Fin 3, (eLpNorm (db i) 2 volume).toReal ^ 2) := by
  let D : ℝ := 4 * ∑ i : Fin 3, (eLpNorm (db i) 2 volume).toReal ^ 2
  let w := fun p : DisplacementPosition × DisplacementPosition =>
    (‖p.2 - p.1‖ ^ 2)⁻¹ * ‖b p.2‖ ^ 2
  have hw0 (p) : 0 ≤ w p := mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (sq_nonneg _)
  have hm : AEStronglyMeasurable w (ν.prod volume) :=
    (((continuous_snd.sub continuous_fst).norm.pow 2).measurable.inv.aestronglyMeasurable).mul
      (hb₂.1.comp_snd.norm.pow 2)
  have hsection (y) : Integrable (fun x => w (y, x)) volume ∧
      (∫ x, w (y, x)) ≤ D := Hardy.estimate b db hb hb₂ hdb₂ y
  have hnorm (y) : (∫ x, ‖w (y, x)‖) = ∫ x, w (y, x) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => Real.norm_of_nonneg (hw0 (y, x))
  have houter : Integrable (fun y => ∫ x, ‖w (y, x)‖) ν := by
    apply (integrable_const D).mono' hm.norm.integral_prod_right'
    exact ae_of_all _ fun y => by
      rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _), hnorm]
      exact (hsection y).2
  have hi : Integrable w (ν.prod volume) :=
    (integrable_prod_iff hm).mpr ⟨ae_of_all _ fun y => (hsection y).1, houter⟩
  refine ⟨hi, ?_⟩
  rw [integral_prod w hi]
  calc
    (∫ y, ∫ x, w (y, x) ∂volume ∂ν) ≤ ∫ _y, D ∂ν :=
      integral_mono_ae hi.integral_prod_left (integrable_const D)
        (ae_of_all _ fun y => (hsection y).2)
    _ = _ := by simp only [integral_const, smul_eq_mul]; rfl

end StandardScalarHardy

end GptLean.Representability
