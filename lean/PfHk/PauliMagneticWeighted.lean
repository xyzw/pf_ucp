import PfHk.PauliMagneticSpin
import PfHk.PauliCarlemanWeights

/-! Integration of the physical quantum Zeeman bound. The weighted
radiation and mass terms are the inputs supplied by the orbital Carleman
estimate. The quantum magnetic error itself is a proved conclusion. -/

noncomputable section
namespace PfHk.PauliMagneticWeighted

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel Gaussian PfHk.PhysicalFieldRegularity
  PfHk.PauliSpin

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

attribute [local irreducible] RadialGauge.momentBound radiationGraphDerivative
  radiationGraphInclusion PauliMagneticSpin.quantum

private theorem scalar_weighted_bound {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (q r m w mw rw : X → ℝ) (K a b : ℝ) (hK : 0 ≤ K)
    (hq : ∀ x, 0 ≤ q x) (hr : ∀ x, 0 ≤ r x) (hm : ∀ x, 0 ≤ m x)
    (hw : ∀ᵐ x ∂ν, 0 ≤ w x)
    (hwr : ∀ᵐ x ∂ν, w x ≤ a * rw x) (hwm : ∀ᵐ x ∂ν, w x ≤ b * mw x)
    (hfield : ∀ x, q x ≤ K * (r x + m x))
    (hmeas : AEStronglyMeasurable (fun x => w x * q x) ν)
    (hiM : Integrable (fun x => mw x * m x) ν)
    (hiR : Integrable (fun x => rw x * r x) ν) :
    Integrable (fun x => w x * q x) ν ∧
      (∫ x, w x * q x ∂ν) ≤
        K * (a * (∫ x, rw x * r x ∂ν) + b * (∫ x, mw x * m x ∂ν)) := by
  let majorant := fun x => K * (a * (rw x * r x) + b * (mw x * m x))
  have hmajor : Integrable majorant ν := ((hiR.const_mul a).add (hiM.const_mul b)).const_mul K
  have hbound : ∀ᵐ x ∂ν, w x * q x ≤ majorant x := by
    filter_upwards [hw, hwr, hwm] with x hx hxr hxm
    have hrad := mul_le_mul_of_nonneg_right hxr (hr x)
    have hmass := mul_le_mul_of_nonneg_right hxm (hm x)
    calc
      _ ≤ w x * (K * (r x + m x)) := mul_le_mul_of_nonneg_left (hfield x) hx
      _ = K * (w x * r x + w x * m x) := by ring
      _ ≤ K * ((a * rw x) * r x + (b * mw x) * m x) :=
        mul_le_mul_of_nonneg_left (add_le_add hrad hmass) hK
      _ = majorant x := by dsimp [majorant]; ring
  have hnonneg : ∀ᵐ x ∂ν, 0 ≤ w x * q x := hw.mono fun x hx => mul_nonneg hx (hq x)
  have hi : Integrable (fun x => w x * q x) ν := hmajor.mono' hmeas (by
    filter_upwards [hbound, hnonneg] with x hx h0
    simpa only [Real.norm_of_nonneg h0] using hx)
  refine ⟨hi, (integral_mono_ae hi hmajor hbound).trans_eq ?_⟩
  dsimp [majorant]
  rw [integral_const_mul, integral_add (hiR.const_mul a) (hiM.const_mul b),
    integral_const_mul, integral_const_mul]

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  {X : Type*} [MeasurableSpace X] {ν : Measure X}

def constant : ℝ := 45 * e ^ 2 * (N : ℝ) ^ 2 * (RadialGauge.momentBound F χ hUV) ^ 2

theorem constant_nonneg : 0 ≤ constant (N := N) F χ hUV e := by
  unfold constant
  positivity

/-- The quantum field is controlled by the supplied weighted radiation
and mass energies, with the actual finite-spin Zeeman action. -/
theorem source_bound
    (positions : X → Fin N → FieldSpace) (q : X → SpinIndex N → RadiationGraphSpace)
    (w massWeight radiationWeight : X → ℝ) {a b : ℝ}
    (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hw : ∀ᵐ x ∂ν, 0 ≤ w x)
    (hwr : ∀ᵐ x ∂ν, w x ≤ a * radiationWeight x)
    (hwm : ∀ᵐ x ∂ν, w x ≤ b * massWeight x)
    (hm : AEStronglyMeasurable (fun x => w x * ∑ s,
      ‖PauliMagneticSpin.quantum F χ hUV C e (positions x) (q x) s‖ ^ 2) ν)
    (hiM : Integrable (fun x => massWeight x *
      ∑ s, ‖radiationGraphInclusion (q x s)‖ ^ 2) ν)
    (hiR : Integrable (fun x => radiationWeight x *
      ∑ s, ‖radiationGraphDerivative (q x s)‖ ^ 2) ν) :
    Integrable (fun x => w x * ∑ s,
      ‖PauliMagneticSpin.quantum F χ hUV C e (positions x) (q x) s‖ ^ 2) ν ∧
      (∫ x, w x * ∑ s,
        ‖PauliMagneticSpin.quantum F χ hUV C e (positions x) (q x) s‖ ^ 2 ∂ν) ≤
        constant (N := N) F χ hUV e *
          (a * (∫ x, radiationWeight x * ∑ s, ‖radiationGraphDerivative (q x s)‖ ^ 2 ∂ν) +
            b * (∫ x, massWeight x * ∑ s, ‖radiationGraphInclusion (q x s)‖ ^ 2 ∂ν)) := by
  apply scalar_weighted_bound
    (fun x => ∑ s, ‖PauliMagneticSpin.quantum F χ hUV C e (positions x) (q x) s‖ ^ 2)
    (fun x => ∑ s, ‖radiationGraphDerivative (q x s)‖ ^ 2)
    (fun x => ∑ s, ‖radiationGraphInclusion (q x s)‖ ^ 2)
    w massWeight radiationWeight (constant (N := N) F χ hUV e) a b
    (constant_nonneg F χ hUV e)
    (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    hw hwr hwm (fun x => PauliMagneticSpin.quantum_sq_le F χ hUV C e (positions x) (q x))
    hm hiM hiR

end PfHk.PauliMagneticWeighted
