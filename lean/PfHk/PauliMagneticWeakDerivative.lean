import GptLean.ElectronicH1Symmetry
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Weak product differentiation for a symmetric field with a varying
label. Only the first line derivative of the label is used. The vectors
are smooth in the field graph norm, so no second field application is
introduced. -/

noncomputable section
namespace PfHk.PauliMagneticWeakDerivative

open MeasureTheory MeasureTheory.Measure GptLean.ElectronicH1Symmetry
open scoped ContDiff InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

variable {E Q K H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem moving_hasLineDerivAt (T : K →L[ℝ] Q →L[ℝ] H)
    {k : E → K} {q : E → Q} {dk : K} {dq : Q} {x v : E}
    (hk : HasLineDerivAt ℝ k dk x v) (hq : HasLineDerivAt ℝ q dq x v) :
    HasLineDerivAt ℝ (fun y => T (k y) (q y))
      (T dk (q x) + T (k x) dq) x v := by
  change HasDerivAt (fun t : ℝ => T (k (x + t • v)) (q (x + t • v))) _ 0
  have hT := T.hasFDerivAt.comp_hasDerivAt 0 hk
  simpa only [Function.comp_def, zero_smul, add_zero] using hT.clm_apply hq

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem map_hasLineDerivAt (J : Q →L[ℝ] H)
    {q : E → Q} {dq : Q} {x v : E} (hq : HasLineDerivAt ℝ q dq x v) :
    HasLineDerivAt ℝ (fun y => J (q y)) (J dq) x v :=
  J.hasFDerivAt.comp_hasDerivAt 0 hq

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem compact_apply (T : K →L[ℝ] Q →L[ℝ] H)
    (k : E → K) {q : E → Q} (hq : HasCompactSupport q) :
    HasCompactSupport (fun x => T (k x) (q x)) := by
  apply hq.mono
  intro x hx hz
  apply hx
  simp only [hz, map_zero]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem memLp_apply (T : K →L[ℝ] Q →L[ℝ] H)
    {k : E → K} {q : E → Q} (hk : Continuous k) (hq : Continuous q)
    (hs : HasCompactSupport q) (μ : Measure E) [IsFiniteMeasureOnCompacts μ] :
    MemLp (fun x => T (k x) (q x)) 2 μ :=
  ((T.continuous.comp hk).clm_apply hq).memLp_of_hasCompactSupport
    (compact_apply T k hs)

/-- Integration by parts and field symmetry give the ordinary/field
cross-term identity on graph-smooth compact vectors. -/
theorem smooth_pairing (μ : Measure E) [IsAddHaarMeasure μ]
    (J : Q →L[ℝ] H) (T : K →L[ℝ] Q →L[ℝ] H)
    (hsym : ∀ k q r, ⟪T k q, J r⟫_ℂ = ⟪J q, T k r⟫_ℂ)
    (k dk : E → K) (hk : Continuous k) (hdk : Continuous dk) (v : E)
    (hderiv : ∀ x, HasLineDerivAt ℝ k (dk x) x v)
    (q r : E → Q) (hq : ContDiff ℝ ∞ q) (hr : ContDiff ℝ ∞ r)
    (hsq : HasCompactSupport q) (hsr : HasCompactSupport r) :
    (∫ x, ⟪J (fderiv ℝ q x v), T (k x) (r x)⟫_ℂ ∂μ) +
      (∫ x, ⟪T (k x) (q x), J (fderiv ℝ r x v)⟫_ℂ ∂μ) =
      -(∫ x, ⟪J (q x), T (dk x) (r x)⟫_ℂ ∂μ) := by
  let dq (x : E) := fderiv ℝ q x v
  let dr (x : E) := fderiv ℝ r x v
  have hdq : Continuous dq := (hq.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdr : Continuous dr := (hr.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsq' : HasCompactSupport dq := hsq.fderiv_apply ℝ v
  have hsr' : HasCompactSupport dr := hsr.fderiv_apply ℝ v
  have hqL : MemLp (fun x => J (q x)) 2 μ :=
    (J.continuous.comp hq.continuous).memLp_of_hasCompactSupport
      (hsq.comp_left (map_zero J))
  have hdqL : MemLp (fun x => J (dq x)) 2 μ :=
    (J.continuous.comp hdq).memLp_of_hasCompactSupport
      (hsq'.comp_left (map_zero J))
  have hkr := memLp_apply T hk hr.continuous hsr μ
  have hdkr := memLp_apply T hdk hr.continuous hsr μ
  have hkdr := memLp_apply T hk hdr hsr' μ
  have hleft := integrable_inner_of_memLp hdqL hkr
  have ha := integrable_inner_of_memLp hqL hdkr
  have hb := integrable_inner_of_memLp hqL hkdr
  have hprod := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := μ) (B := innerBilinear)
    hleft (integrable_inner_of_memLp hqL (hdkr.add hkdr))
    (integrable_inner_of_memLp hqL hkr)
    (fun x _ => map_hasLineDerivAt J
      ((hq.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt v))
    (fun x _ => moving_hasLineDerivAt T (hderiv x)
      ((hr.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt v))
  change (∫ x, ⟪J (q x), T (dk x) (r x) + T (k x) (dr x)⟫_ℂ ∂μ) =
    -(∫ x, ⟪J (dq x), T (k x) (r x)⟫_ℂ ∂μ) at hprod
  simp only [inner_add_right] at hprod
  rw [integral_add ha hb] at hprod
  have hsymint : (∫ x, ⟪T (k x) (q x), J (dr x)⟫_ℂ ∂μ) =
      ∫ x, ⟪J (q x), T (k x) (dr x)⟫_ℂ ∂μ := by
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hsym _ _ _)
  change (∫ x, ⟪J (dq x), T (k x) (r x)⟫_ℂ ∂μ) +
    (∫ x, ⟪T (k x) (q x), J (dr x)⟫_ℂ ∂μ) = _
  rw [hsymint]
  linear_combination hprod

end PfHk.PauliMagneticWeakDerivative
