import GptLean.ElectronicH1Space
import GptLean.SymmetricLift.L2Dominated
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-! Expanding smooth cutoffs and strong convergence in the actual H1 graph. -/

noncomputable section

namespace GptLean.ElectronicH1Core

open MeasureTheory Filter GptLean.SymmetricLift GptLean.Repair GptLean.ElectronicH1Space
open scoped ENNReal Topology ContDiff

variable {d : ℕ} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def cutoff (d n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) where
  rIn := (n : ℝ) + 1
  rOut := 2 * ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by have := Nat.cast_nonneg (α := ℝ) n; linarith

theorem cutoff_scaled (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    cutoff d n x = cutoff d 0 (((n : ℝ) + 1)⁻¹ • x) := by
  simp only [ContDiffBump.apply, cutoff, Nat.cast_zero, zero_add, mul_one, div_one,
    sub_zero, inv_one, one_smul]
  congr 2
  field_simp

def cutoffDerivative (n : ℕ) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fderiv ℝ (cutoff d n) x (EuclideanSpace.single i 1)

theorem cutoffDerivative_scaled (n : ℕ) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    cutoffDerivative n i x = ((n : ℝ) + 1)⁻¹ *
      fderiv ℝ (cutoff d 0) (((n : ℝ) + 1)⁻¹ • x) (EuclideanSpace.single i 1) := by
  have heq : (cutoff d n : EuclideanSpace ℝ (Fin d) → ℝ) =
      fun y => cutoff d 0 (((n : ℝ) + 1)⁻¹ • y) := funext (cutoff_scaled n)
  have h := (((cutoff d 0).contDiff (n := ⊤)).differentiable (by simp)
    (((n : ℝ) + 1)⁻¹ • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul (((n : ℝ) + 1)⁻¹))
  unfold cutoffDerivative
  rw [heq]
  change fderiv ℝ ((cutoff d 0) ∘ fun y => ((n : ℝ) + 1)⁻¹ • y) x _ = _
  rw [h.fderiv]
  simp

theorem cutoff_tendsto (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n => cutoff d n x) atTop (𝓝 1) := by
  have hs : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • x) atTop (𝓝 0) := by
    simpa only [one_div, zero_smul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x
  have hzero : cutoff d 0 (0 : EuclideanSpace ℝ (Fin d)) = 1 :=
    (cutoff d 0).one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [cutoff]))
  simpa only [Function.comp_def, ← cutoff_scaled, hzero] using ((cutoff d 0).continuous.tendsto 0).comp hs

theorem cutoffDerivative_tendsto (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n => cutoffDerivative n i x) atTop (𝓝 0) := by
  have hc := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hx : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • x) atTop (𝓝 0) := by
    simpa only [one_div, zero_smul] using hc.smul_const x
  have hd : Continuous (fun y =>
      fderiv ℝ (cutoff d 0) y (EuclideanSpace.single i 1)) :=
    (((cutoff d 0).contDiff (n := ⊤)).continuous_fderiv (by simp)).clm_apply continuous_const
  simpa only [Function.comp_def, cutoffDerivative_scaled, one_div, zero_mul] using hc.mul ((hd.tendsto 0).comp hx)

theorem exists_cutoffDerivative_bound (d : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n i (x : EuclideanSpace ℝ (Fin d)),
      |cutoffDerivative n i x| ≤ B := by
  obtain ⟨B, hB⟩ := (((cutoff d 0).contDiff (n := ⊤)).continuous_fderiv (by simp)).bounded_above_of_compact_support ((cutoff d 0).hasCompactSupport.fderiv ℝ)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨B, hB0, ?_⟩
  intro n i x
  rw [cutoffDerivative_scaled, abs_mul, abs_of_nonneg (by positivity)]
  have hcoef : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hder : |fderiv ℝ (cutoff d 0) (((n : ℝ) + 1)⁻¹ • x)
      (EuclideanSpace.single i 1)| ≤ B := by
    simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using
      (fderiv ℝ (cutoff d 0) (((n : ℝ) + 1)⁻¹ • x)).le_of_opNorm_le
        (hB (((n : ℝ) + 1)⁻¹ • x)) (EuclideanSpace.single i 1)
  calc
    _ ≤ 1 * B := mul_le_mul hcoef hder (abs_nonneg _) (by positivity)
    _ = B := one_mul B

def cutoffValue (u : H1 E (Fin d)) (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : E :=
  cutoff d n x • value u x

def cutoffGradient (u : H1 E (Fin d)) (n : ℕ) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : E :=
  cutoff d n x • derivative i u x + cutoffDerivative n i x • value u x

theorem cutoffValue_memLp (u : H1 E (Fin d)) (n : ℕ) :
    MemLp (cutoffValue u n) 2 volume :=
  (Lp.memLp (value u)).smul ((cutoff d n).continuous.memLp_top_of_hasCompactSupport
    (cutoff d n).hasCompactSupport volume)

theorem cutoffGradient_memLp (u : H1 E (Fin d)) (n : ℕ) (i : Fin d) :
    MemLp (cutoffGradient u n i) 2 volume := by
  have hd : Continuous (cutoffDerivative n i) :=
    (((cutoff d n).contDiff (n := ⊤)).continuous_fderiv (by simp)).clm_apply continuous_const
  exact ((Lp.memLp (derivative i u)).smul
    ((cutoff d n).continuous.memLp_top_of_hasCompactSupport
      (cutoff d n).hasCompactSupport volume)).add
    ((Lp.memLp (value u)).smul (hd.memLp_top_of_hasCompactSupport
      ((cutoff d n).hasCompactSupport.fderiv_apply ℝ _) volume))

theorem cutoff_weak (u : H1 E (Fin d)) (n : ℕ) :
    HasWeakH1Local (cutoffValue u n) (cutoffGradient u n) :=
  weakH1Local_smooth_real_smul (weak u) (cutoff d n).contDiff

def cutoffH1 (u : H1 E (Fin d)) (n : ℕ) : H1 E (Fin d) :=
  ofFunctions (cutoffValue u n) (cutoffGradient u n)
    (cutoffValue_memLp u n) (cutoffGradient_memLp u n) (cutoff_weak u n)

theorem cutoffValue_hasCompactSupport (u : H1 E (Fin d)) (n : ℕ) :
    HasCompactSupport (cutoffValue u n) := (cutoff d n).hasCompactSupport.smul_right

theorem cutoffGradient_hasCompactSupport (u : H1 E (Fin d)) (n : ℕ) (i : Fin d) :
    HasCompactSupport (cutoffGradient u n i) :=
  (cutoff d n).hasCompactSupport.smul_right.add
    ((cutoff d n).hasCompactSupport.fderiv_apply ℝ _).smul_right

omit [CompleteSpace E] in
private theorem norm_smul_add_sq_le (a b B : ℝ) (v w : E)
    (_hB : 0 ≤ B) (ha : |a| ≤ 1) (hb : |b| ≤ B) :
    ‖a • v + b • w‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * B ^ 2 * ‖w‖ ^ 2 := by
  have htri := norm_add_le (a • v) (b • w)
  have hv : ‖a • v‖ ≤ ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (norm_nonneg v)
  have hw : ‖b • w‖ ≤ B * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg w)
  nlinarith [sq_nonneg (‖v‖ - B * ‖w‖), norm_nonneg (a • v + b • w),
    norm_nonneg v, norm_nonneg w]

private theorem sq_le_two_sq_add (a b B : ℝ) : a ^ 2 ≤ 2 * a ^ 2 + 2 * B ^ 2 * b ^ 2 := by
  nlinarith [sq_nonneg a, sq_nonneg (B * b)]

omit [CompleteSpace E] in
private theorem cutoff_mul_eLpNorm_tendsto (f : L2 E (Fin d)) :
    Tendsto (fun n => eLpNorm ((fun x => cutoff d n x • f x) - (fun x => f x)) 2 volume)
      atTop (𝓝 0) := by
  apply tendsto_eLpNorm_two_of_dominated_sq
    (b := fun x => ‖f x‖ ^ 2)
    (fun n => (cutoff d n).continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f))
    (Lp.aestronglyMeasurable f)
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f))
  · intro n
    exact Eventually.of_forall fun x => by
      simp only [Pi.smul_apply']
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff d n).nonneg]
      apply pow_le_pow_left₀ (mul_nonneg (cutoff d n).nonneg (norm_nonneg _))
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right ((cutoff d n).le_one (x := x)) (norm_nonneg (f x))
  · exact Eventually.of_forall fun _ => le_rfl
  · exact Eventually.of_forall fun x => by
      simpa only [Pi.smul_apply', Pi.smul_apply, one_smul] using
        (cutoff_tendsto x).smul_const (f x)

omit [CompleteSpace E] in
private theorem cutoff_gradient_eLpNorm_tendsto (f g : L2 E (Fin d)) (i : Fin d) :
    Tendsto (fun n => eLpNorm
      ((fun x => cutoff d n x • g x + cutoffDerivative n i x • f x) - (fun x => g x)) 2 volume)
      atTop (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := exists_cutoffDerivative_bound d
  have hsq (v : L2 E (Fin d)) : Integrable (fun x => ‖v x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hdm (n : ℕ) : AEStronglyMeasurable (cutoffDerivative n i) volume :=
    ((((cutoff d n).contDiff (n := ⊤)).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable
  apply tendsto_eLpNorm_two_of_dominated_sq
    (b := fun x => 2 * ‖g x‖ ^ 2 + 2 * B ^ 2 * ‖f x‖ ^ 2)
    (fun n => ((cutoff d n).continuous.aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable g)).add ((hdm n).smul (Lp.aestronglyMeasurable f)))
    (Lp.aestronglyMeasurable g)
    (((hsq g).const_mul 2).add ((hsq f).const_mul (2 * B ^ 2)))
  · intro n
    exact Eventually.of_forall fun x => norm_smul_add_sq_le _ _ B _ _ hB0
      (by rw [abs_of_nonneg (cutoff d n).nonneg]; exact (cutoff d n).le_one) (hB n i x)
  · exact Eventually.of_forall fun _ => sq_le_two_sq_add _ _ B
  · exact Eventually.of_forall fun x => by
      simpa only [Pi.smul_apply', Pi.smul_apply, Pi.add_apply, one_smul, zero_smul, add_zero] using
        ((cutoff_tendsto x).smul_const (g x)).add
          ((cutoffDerivative_tendsto i x).smul_const (f x))

theorem cutoffH1_tendsto (u : H1 E (Fin d)) :
    Tendsto (cutoffH1 u) atTop (𝓝 u) := by
  have hv : Tendsto (fun n => (cutoffValue_memLp u n).toLp (cutoffValue u n))
      atTop (𝓝 (value u)) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (cutoffValue u)
      (cutoffValue_memLp u) (value u) (Lp.memLp (value u))).mpr
      (cutoff_mul_eLpNorm_tendsto (value u))
    simpa only [Lp.toLp_coeFn] using h
  have hd (i : Fin d) :
      Tendsto (fun n => (cutoffGradient_memLp u n i).toLp (cutoffGradient u n i))
        atTop (𝓝 (derivative i u)) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => cutoffGradient u n i)
      (fun n => cutoffGradient_memLp u n i) (derivative i u) (Lp.memLp (derivative i u))).mpr
      (cutoff_gradient_eLpNorm_tendsto (value u) (derivative i u) i)
    simpa only [Lp.toLp_coeFn] using h
  exact tendsto_subtype_rng.mpr (hv.prodMk_nhds (tendsto_pi_nhds.mpr hd))

end GptLean.ElectronicH1Core
