import GptLean.RepresentabilityCoherentSobolev
import GptLean.Repair.CovariantProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
The norm of a weakly differentiable Hilbert-valued field is weakly
differentiable. Its weak gradient is the real inner product with the
weak derivative, divided by the norm. The bounded smooth maps
`ε t / (1 + ε t)`, with `t = √(‖v‖² + ε²) - ε`, are passed through the
proved bounded chain rule. Dominated convergence then removes `ε`.
-/

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

namespace GptLean.NormWeakH1

open MeasureTheory Filter SymmetricLift
open scoped ENNReal Topology ContDiff RealInnerProductSpace

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- The regularization parameter `1 / (n + 1)`. -/
def scale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem scale_pos (n : ℕ) : 0 < scale n := by
  unfold scale
  positivity

theorem scale_le_one (n : ℕ) : scale n ≤ 1 := by
  unfold scale
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem tendsto_scale : Tendsto scale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The smooth norm `√(‖v‖² + ε²)`. -/
def smoothNorm (ε : ℝ) (v : P) : ℝ := Real.sqrt (‖v‖ ^ 2 + ε ^ 2)

/-- The shifted smooth norm `√(‖v‖² + ε²) - ε`. -/
def shiftedNorm (ε : ℝ) (v : P) : ℝ := smoothNorm ε v - ε

/-- The bounded approximant `ε t / (1 + ε t)` of `ε ‖v‖`. -/
def boundedNorm (ε : ℝ) (v : P) : ℝ := ε * shiftedNorm ε v / (1 + ε * shiftedNorm ε v)

/-- The derivative of the bounded approximant. -/
def boundedNormDeriv (ε : ℝ) (v : P) : P →L[ℝ] ℝ :=
  (ε / ((1 + ε * shiftedNorm ε v) ^ 2 * smoothNorm ε v)) • innerSL ℝ v

theorem smoothNorm_pos {ε : ℝ} (hε : 0 < ε) (v : P) : 0 < smoothNorm ε v :=
  Real.sqrt_pos.mpr (by positivity)

theorem norm_le_smoothNorm (ε : ℝ) (v : P) : ‖v‖ ≤ smoothNorm ε v := by
  have h := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε) : ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 + ε ^ 2)
  rwa [Real.sqrt_sq (norm_nonneg v)] at h

theorem le_smoothNorm {ε : ℝ} (hε : 0 ≤ ε) (v : P) : ε ≤ smoothNorm ε v := by
  have h := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg ‖v‖) : ε ^ 2 ≤ ‖v‖ ^ 2 + ε ^ 2)
  rwa [Real.sqrt_sq hε] at h

theorem smoothNorm_le {ε : ℝ} (hε : 0 ≤ ε) (v : P) : smoothNorm ε v ≤ ‖v‖ + ε := by
  have hle : ‖v‖ ^ 2 + ε ^ 2 ≤ (‖v‖ + ε) ^ 2 := by nlinarith [norm_nonneg v]
  exact (Real.sqrt_le_sqrt hle).trans_eq (Real.sqrt_sq (by positivity))

theorem shiftedNorm_nonneg {ε : ℝ} (hε : 0 ≤ ε) (v : P) : 0 ≤ shiftedNorm ε v :=
  sub_nonneg.mpr (le_smoothNorm hε v)

theorem shiftedNorm_le {ε : ℝ} (hε : 0 ≤ ε) (v : P) : shiftedNorm ε v ≤ ‖v‖ := by
  unfold shiftedNorm
  linarith [smoothNorm_le hε v]

theorem one_add_pos {ε : ℝ} (hε : 0 ≤ ε) (v : P) : 0 < 1 + ε * shiftedNorm ε v := by
  have := mul_nonneg hε (shiftedNorm_nonneg hε v)
  linarith

theorem norm_boundedNorm_le {ε : ℝ} (hε : 0 ≤ ε) (v : P) : ‖boundedNorm ε v‖ ≤ 1 := by
  have ht := mul_nonneg hε (shiftedNorm_nonneg hε v)
  have hd := one_add_pos hε v
  unfold boundedNorm
  rw [Real.norm_of_nonneg (div_nonneg ht hd.le), div_le_one hd]
  linarith

theorem continuous_smoothNorm (ε : ℝ) : Continuous (smoothNorm (P := P) ε) :=
  ((continuous_norm.pow 2).add continuous_const).sqrt

theorem continuous_shiftedNorm (ε : ℝ) : Continuous (shiftedNorm (P := P) ε) :=
  (continuous_smoothNorm ε).sub continuous_const

theorem continuous_boundedNorm {ε : ℝ} (hε : 0 ≤ ε) : Continuous (boundedNorm (P := P) ε) :=
  (continuous_const.mul (continuous_shiftedNorm ε)).div
    (continuous_const.add (continuous_const.mul (continuous_shiftedNorm ε)))
    (fun v => (one_add_pos hε v).ne')

theorem continuous_boundedNormDeriv {ε : ℝ} (hε : 0 < ε) :
    Continuous (boundedNormDeriv (P := P) ε) := by
  have hc : Continuous (fun v : P => ε / ((1 + ε * shiftedNorm ε v) ^ 2 * smoothNorm ε v)) :=
    continuous_const.div
      (((continuous_const.add (continuous_const.mul (continuous_shiftedNorm ε))).pow 2).mul
        (continuous_smoothNorm ε))
      (fun v => (mul_pos (pow_pos (one_add_pos hε.le v) 2) (smoothNorm_pos hε v)).ne')
  exact hc.smul (innerSL ℝ (E := P)).continuous

theorem hasFDerivAt_boundedNorm {ε : ℝ} (hε : 0 < ε) (v : P) :
    HasFDerivAt (boundedNorm ε) (boundedNormDeriv ε v) v := by
  have hq : HasFDerivAt (fun w : P => ‖w‖ ^ 2 + ε ^ 2) (2 • innerSL ℝ v) v :=
    (hasStrictFDerivAt_norm_sq v).hasFDerivAt.add_const _
  have hs := hq.sqrt (by positivity)
  have hεt := (hs.sub_const ε).const_mul ε
  have hden := hεt.const_add 1
  have hd0 : (1 + ε * (Real.sqrt (‖v‖ ^ 2 + ε ^ 2) - ε)) ≠ 0 := (one_add_pos hε.le v).ne'
  have hinv := (hasDerivAt_inv hd0).comp_hasFDerivAt v hden
  have hprod := hεt.mul hinv
  have hfun : boundedNorm ε = fun w : P =>
      ε * (Real.sqrt (‖w‖ ^ 2 + ε ^ 2) - ε) *
        ((fun y : ℝ => y⁻¹) ∘ fun w : P => 1 + ε * (Real.sqrt (‖w‖ ^ 2 + ε ^ 2) - ε)) w := by
    funext w
    simp only [boundedNorm, shiftedNorm, smoothNorm, Function.comp_apply, div_eq_mul_inv]
  rw [hfun]
  apply hprod.congr_fderiv
  have hsq := smoothNorm_pos hε v
  have hd := one_add_pos hε.le v
  unfold boundedNormDeriv shiftedNorm at *
  unfold smoothNorm at *
  ext w
  simp only [add_apply, smul_apply, smul_eq_mul,
    innerSL_apply_apply, Function.comp_apply, nsmul_eq_mul, Nat.cast_ofNat]
  field_simp
  ring

theorem norm_boundedNormDeriv_apply_le {ε : ℝ} (hε : 0 < ε) (v w : P) :
    ‖boundedNormDeriv ε v w‖ ≤ ε * ‖w‖ := by
  have hs := smoothNorm_pos hε v
  have hd := one_add_pos hε.le v
  have hd1 : 1 ≤ (1 + ε * shiftedNorm ε v) ^ 2 := by
    nlinarith [mul_nonneg hε.le (shiftedNorm_nonneg hε.le v)]
  have hc : 0 ≤ ε / ((1 + ε * shiftedNorm ε v) ^ 2 * smoothNorm ε v) := by positivity
  simp only [boundedNormDeriv, smul_apply, innerSL_apply_apply, smul_eq_mul,
    norm_mul, Real.norm_of_nonneg hc]
  have hi : ‖⟪v, w⟫‖ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm v w
  calc
    _ ≤ ε / ((1 + ε * shiftedNorm ε v) ^ 2 * smoothNorm ε v) * (smoothNorm ε v * ‖w‖) :=
      mul_le_mul_of_nonneg_left (hi.trans
        (mul_le_mul_of_nonneg_right (norm_le_smoothNorm ε v) (norm_nonneg w))) hc
    _ = ε / (1 + ε * shiftedNorm ε v) ^ 2 * ‖w‖ := by
      field_simp
    _ ≤ ε * ‖w‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
      exact div_le_self hε.le hd1

/-! Rescaled approximants and their pointwise limits. -/

theorem rescaled_boundedNorm {ε : ℝ} (hε : 0 < ε) (v : P) :
    ε⁻¹ * boundedNorm ε v = shiftedNorm ε v / (1 + ε * shiftedNorm ε v) := by
  unfold boundedNorm
  field_simp

theorem rescaled_boundedNormDeriv {ε : ℝ} (hε : 0 < ε) (v w : P) :
    ε⁻¹ * boundedNormDeriv ε v w =
      ⟪v, w⟫ / ((1 + ε * shiftedNorm ε v) ^ 2 * smoothNorm ε v) := by
  have hs := smoothNorm_pos hε v
  have hd := one_add_pos hε.le v
  simp only [boundedNormDeriv, smul_apply, innerSL_apply_apply, smul_eq_mul]
  field_simp

theorem abs_rescaled_boundedNorm_le {ε : ℝ} (hε : 0 < ε) (v : P) :
    ‖ε⁻¹ * boundedNorm ε v‖ ≤ ‖v‖ := by
  rw [rescaled_boundedNorm hε v]
  have ht := shiftedNorm_nonneg hε.le v
  have hd := one_add_pos hε.le v
  rw [Real.norm_of_nonneg (div_nonneg ht hd.le), div_le_iff₀ hd]
  nlinarith [shiftedNorm_le hε.le v, mul_nonneg hε.le ht, norm_nonneg v]

theorem abs_rescaled_boundedNormDeriv_le {ε : ℝ} (hε : 0 < ε) (v w : P) :
    ‖ε⁻¹ * boundedNormDeriv ε v w‖ ≤ ‖w‖ := by
  rw [norm_mul, norm_inv, Real.norm_of_nonneg hε.le]
  calc
    _ ≤ ε⁻¹ * (ε * ‖w‖) :=
      mul_le_mul_of_nonneg_left (norm_boundedNormDeriv_apply_le hε v w) (inv_nonneg.mpr hε.le)
    _ = ‖w‖ := by field_simp

theorem tendsto_smoothNorm (v : P) :
    Tendsto (fun n => smoothNorm (scale n) v) atTop (𝓝 ‖v‖) := by
  have hc : Continuous (fun ε : ℝ => Real.sqrt (‖v‖ ^ 2 + ε ^ 2)) :=
    (continuous_const.add (continuous_pow 2)).sqrt
  have h := (hc.tendsto 0).comp tendsto_scale
  simpa only [Function.comp_def, smoothNorm, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, Real.sqrt_sq (norm_nonneg v)] using h

theorem tendsto_shiftedNorm (v : P) :
    Tendsto (fun n => shiftedNorm (scale n) v) atTop (𝓝 ‖v‖) := by
  have h : Tendsto (fun n => shiftedNorm (scale n) v) atTop (𝓝 (‖v‖ - 0)) :=
    (tendsto_smoothNorm v).sub tendsto_scale
  simpa only [sub_zero] using h

theorem tendsto_rescaled_boundedNorm (v : P) :
    Tendsto (fun n => (scale n)⁻¹ * boundedNorm (scale n) v) atTop (𝓝 ‖v‖) := by
  have hd : Tendsto (fun n => 1 + scale n * shiftedNorm (scale n) v) atTop (𝓝 (1 + 0 * ‖v‖)) :=
    tendsto_const_nhds.add (tendsto_scale.mul (tendsto_shiftedNorm v))
  have h := (tendsto_shiftedNorm v).div hd (by simp)
  simp only [zero_mul, add_zero, div_one] at h
  exact h.congr fun n => (rescaled_boundedNorm (scale_pos n) v).symm

theorem tendsto_rescaled_boundedNormDeriv (v w : P) :
    Tendsto (fun n => (scale n)⁻¹ * boundedNormDeriv (scale n) v w) atTop
      (𝓝 (⟪v, w⟫ / ‖v‖)) := by
  have he : ∀ n, (scale n)⁻¹ * boundedNormDeriv (scale n) v w =
      ⟪v, w⟫ / ((1 + scale n * shiftedNorm (scale n) v) ^ 2 * smoothNorm (scale n) v) :=
    fun n => rescaled_boundedNormDeriv (scale_pos n) v w
  by_cases hv : v = 0
  · subst hv
    simp only [inner_zero_left, zero_div] at he ⊢
    exact tendsto_const_nhds.congr fun n => (he n).symm
  have hd : Tendsto (fun n => (1 + scale n * shiftedNorm (scale n) v) ^ 2 *
      smoothNorm (scale n) v) atTop (𝓝 ((1 + 0 * ‖v‖) ^ 2 * ‖v‖)) :=
    ((tendsto_const_nhds.add (tendsto_scale.mul (tendsto_shiftedNorm v))).pow 2).mul
      (tendsto_smoothNorm v)
  have hne : (1 + 0 * ‖v‖) ^ 2 * ‖v‖ ≠ 0 := by simpa using hv
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ⟪v, w⟫) atTop (𝓝 ⟪v, w⟫)).div hd hne
  simp only [zero_mul, add_zero, one_pow, one_mul] at h
  exact h.congr fun n => (he n).symm

theorem norm_inner_div_norm_le (v w : P) : ‖⟪v, w⟫ / ‖v‖‖ ≤ ‖w‖ := by
  by_cases hv : v = 0
  · subst hv
    simp
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [norm_div, norm_norm, div_le_iff₀ hp, mul_comm]
  exact norm_inner_le_norm v w

section Closure

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weak H1 identities pass to almost-everywhere limits under local L2
domination of both the functions and their weak derivatives. -/
theorem weakH1Local_of_dominated_limit
    {f : ℕ → EuclideanSpace ℝ (Fin d) → E}
    {df : ℕ → Fin d → EuclideanSpace ℝ (Fin d) → E}
    {g : EuclideanSpace ℝ (Fin d) → E} {dg : Fin d → EuclideanSpace ℝ (Fin d) → E}
    {F : EuclideanSpace ℝ (Fin d) → ℝ} {DF : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ∀ n, HasWeakH1Local (f n) (df n))
    (hF : ∀ K, IsCompact K → MemLp F 2 (volume.restrict K))
    (hDF : ∀ i K, IsCompact K → MemLp (DF i) 2 (volume.restrict K))
    (hg : AEStronglyMeasurable g volume) (hdg : ∀ i, AEStronglyMeasurable (dg i) volume)
    (hfb : ∀ n, ∀ᵐ x ∂volume, ‖f n x‖ ≤ F x)
    (hdfb : ∀ n i, ∀ᵐ x ∂volume, ‖df n i x‖ ≤ DF i x)
    (hgb : ∀ᵐ x ∂volume, ‖g x‖ ≤ F x) (hdgb : ∀ i, ∀ᵐ x ∂volume, ‖dg i x‖ ≤ DF i x)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hdlim : ∀ i, ∀ᵐ x ∂volume, Tendsto (fun n => df n i x) atTop (𝓝 (dg i x))) :
    HasWeakH1Local g dg := by
  have hgK : ∀ K, IsCompact K → MemLp g 2 (volume.restrict K) := fun K hK =>
    (hF K hK).mono' hg.restrict (ae_restrict_of_ae hgb)
  have hdgK : ∀ i K, IsCompact K → MemLp (dg i) 2 (volume.restrict K) := fun i K hK =>
    (hDF i K hK).mono' (hdg i).restrict (ae_restrict_of_ae (hdgb i))
  refine ⟨hgK, hdgK, ?_⟩
  intro i φ hφ hs
  let K := tsupport φ
  have hK : IsCompact K := hs
  let φ' := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hφ' : Continuous φ' := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmφ : MemLp φ 2 (volume.restrict K) :=
    (hφ.continuous.memLp_of_hasCompactSupport hs).restrict K
  have hmφ' : MemLp φ' 2 (volume.restrict K) :=
    (hφ'.memLp_of_hasCompactSupport (hs.fderiv_apply ℝ _)).restrict K
  have hz : ∀ x, x ∉ K → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hz' : ∀ x, x ∉ K → φ' x = 0 := fun x hx => by
    simp [φ', fderiv_of_notMem_tsupport ℝ hx]
  have hconv : Tendsto (fun n => eLpNorm (f n - g) 2 (volume.restrict K)) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_dominated_sq (fun n => ((hf n).function_memLp K hK).1)
      hg.restrict (hF K hK).integrable_sq
    · intro n
      filter_upwards [ae_restrict_of_ae (hfb n)] with x hx
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    · filter_upwards [ae_restrict_of_ae hgb] with x hx
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    · exact ae_restrict_of_ae hlim
  have hdconv : Tendsto (fun n => eLpNorm (df n i - dg i) 2 (volume.restrict K))
      atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_dominated_sq
      (fun n => ((hf n).derivative_memLp i K hK).1) (hdg i).restrict (hDF i K hK).integrable_sq
    · intro n
      filter_upwards [ae_restrict_of_ae (hdfb n i)] with x hx
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    · filter_upwards [ae_restrict_of_ae (hdgb i)] with x hx
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    · exact ae_restrict_of_ae (hdlim i)
  have hweak (n : ℕ) : (∫ x in K, φ x • df n i x) = -(∫ x in K, φ' x • f n x) := by
    rw [← integral_smul_eq_setIntegral _ hz, ← integral_smul_eq_setIntegral _ hz']
    exact (hf n).weak i φ hφ hs
  have hfinal := weak_derivative_identity_closed_eLpNorm (f := f) (df := fun n => df n i)
    hmφ hmφ' (fun n => (hf n).function_memLp K hK) (fun n => (hf n).derivative_memLp i K hK)
    (hgK K hK) (hdgK i K hK) hconv hdconv (Eventually.of_forall hweak)
  rw [integral_smul_eq_setIntegral _ hz, integral_smul_eq_setIntegral _ hz']
  exact hfinal

end Closure

section Chain

variable {d : ℕ} [CompleteSpace P]

set_option backward.isDefEq.respectTransparency.types false in
/-- Each bounded approximant acts on a weak H1 field by the classical chain rule. -/
theorem boundedNorm_weakH1Local {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {u : EuclideanSpace ℝ (Fin d) → P} {du : Fin d → EuclideanSpace ℝ (Fin d) → P}
    (hu : HasWeakH1Local u du) :
    HasWeakH1Local (fun x => boundedNorm ε (u x))
      (fun i x => boundedNormDeriv ε (u x) (du i x)) := by
  have h := Representability.weakH1Local_bounded_split_chain (d := d) (P := P) (E := ℝ)
    (fun p => boundedNorm ε p.2) (fun p => boundedNormDeriv ε p.2)
    (fun _ _ => (0 : P →L[ℝ] ℝ)) (fun _ _ => (0 : ℝ))
    ((continuous_boundedNorm hε.le).comp continuous_snd)
    ((continuous_boundedNormDeriv hε).comp continuous_snd)
    (fun _ => continuous_const) (fun _ => continuous_const)
    (fun p => norm_boundedNorm_le hε.le p.2)
    (fun p w => (norm_boundedNormDeriv_apply_le hε p.2 w).trans
      (mul_le_of_le_one_left (norm_nonneg w) hε1))
    (fun _ _ w => by simp) (fun _ _ => by simp)
    (fun v i x dv hv => by
      have hv' : HasDerivAt (fun t : ℝ => v (x + t • EuclideanSpace.single i 1)) dv 0 := hv
      have h := (hasFDerivAt_boundedNorm hε (v x)).comp_hasDerivAt_of_eq (0 : ℝ) hv' (by simp)
      change HasDerivAt (fun t : ℝ => boundedNorm ε (v (x + t • EuclideanSpace.single i 1)))
        (boundedNormDeriv ε (v x) dv + (0 : P →L[ℝ] ℝ) (v x) + 0) 0
      rw [zero_apply, add_zero, add_zero]
      exact h)
    hu
  exact h.congr (ae_of_all _ fun _ => rfl)
    (fun i => ae_of_all _ fun x => by simp only [zero_apply, add_zero])

/-- The norm chain rule for weak H1 fields with values in a real Hilbert space.
On the zero set of the field the gradient vanishes by the convention `0 / 0 = 0`. -/
theorem norm_weakH1Local {u : EuclideanSpace ℝ (Fin d) → P}
    {du : Fin d → EuclideanSpace ℝ (Fin d) → P} (hu : HasWeakH1Local u du) :
    HasWeakH1Local (fun x => ‖u x‖) (fun i x => ⟪u x, du i x⟫ / ‖u x‖) := by
  have hum := (localMemLp_two_locallyIntegrable hu.function_memLp).aestronglyMeasurable
  have hdum (i : Fin d) :=
    (localMemLp_two_locallyIntegrable (hu.derivative_memLp i)).aestronglyMeasurable
  have hn (n : ℕ) := Repair.weakH1Local_map ((scale n)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    (boundedNorm_weakH1Local (scale_pos n) (scale_le_one n) hu)
  apply weakH1Local_of_dominated_limit
    (f := fun n x => (scale n)⁻¹ * boundedNorm (scale n) (u x))
    (df := fun n i x => (scale n)⁻¹ * boundedNormDeriv (scale n) (u x) (du i x))
    (F := fun x => ‖u x‖) (DF := fun i x => ‖du i x‖)
  · intro n
    exact (hn n).congr (ae_of_all _ fun _ => rfl) (fun i => ae_of_all _ fun _ => rfl)
  · intro K hK
    exact (hu.function_memLp K hK).norm
  · intro i K hK
    exact (hu.derivative_memLp i K hK).norm
  · exact hum.norm
  · intro i
    exact ((hum.inner (hdum i)).aemeasurable.div hum.norm.aemeasurable).aestronglyMeasurable
  · intro n
    exact ae_of_all _ fun x => abs_rescaled_boundedNorm_le (scale_pos n) (u x)
  · intro n i
    exact ae_of_all _ fun x => abs_rescaled_boundedNormDeriv_le (scale_pos n) (u x) (du i x)
  · exact ae_of_all _ fun x => (norm_norm (u x)).le
  · intro i
    exact ae_of_all _ fun x => norm_inner_div_norm_le (u x) (du i x)
  · exact ae_of_all _ fun x => tendsto_rescaled_boundedNorm (u x)
  · intro i
    exact ae_of_all _ fun x => tendsto_rescaled_boundedNormDeriv (u x) (du i x)

/-- Pointwise bound for the norm gradient. -/
theorem norm_normGradient_le (v w : P) : ‖⟪v, w⟫ / ‖v‖‖ ≤ ‖w‖ :=
  norm_inner_div_norm_le v w

end Chain

end GptLean.NormWeakH1
