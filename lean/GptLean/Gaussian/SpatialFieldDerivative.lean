import GptLean.Gaussian.SpatialField
import GptLean.SymmetricLift.L2Dominated
import GptLean.Repair.MeasuredTagSobolev
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Sequences

/-!
Strong L² differentiation of the actual cutoff Fourier kernels. The
pointwise derivative and the soft momentum support give a common square
integrable bound on difference quotients. Dominated convergence therefore
identifies the derivative in one-photon L², before applying the first-chaos
map. These are Hilbert-space derivatives, not yet pathwise derivatives of
the jointly measurable Gaussian representatives.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem softDerivativeKernel_slope_bound
    (momentum : Ω → FieldSpace) (ds : List (Fin 3)) (j : Fin 3)
    {k : ℝ} (hk : 0 ≤ k) (x : FieldSpace) (g : Ω → ℂ) (y : Ω) (t : ℝ) :
    ‖t⁻¹ • (softDerivativeKernel momentum ds k
      (x + t • EuclideanSpace.single j 1) g y -
        softDerivativeKernel momentum ds k x g y)‖ ≤
      k ^ (ds.length + 1) * ‖softBase momentum k g y‖ := by
  have hd := fun s => softDerivativeKernel_hasDerivAt momentum ds j k x g y s
  have hb : ∀ s : ℝ, ‖deriv (fun t : ℝ => softDerivativeKernel momentum ds k
      (x + t • EuclideanSpace.single j 1) g y) s‖ ≤
      k ^ (ds.length + 1) * ‖softBase momentum k g y‖ := by
    intro s
    rw [(hd s).deriv]
    exact norm_softDerivativeKernel_le momentum (j :: ds) hk _ g y
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s (_ : s ∈ Set.univ) => (hd s).differentiableAt)
    (fun s (_ : s ∈ Set.univ) => hb s) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  simp only [zero_smul, add_zero, sub_zero] at h
  by_cases ht : t = 0
  · simp [ht]
    positivity
  · rw [norm_smul, norm_inv]
    calc
      _ ≤ ‖t‖⁻¹ * ((k ^ (ds.length + 1) * ‖softBase momentum k g y‖) * ‖t‖) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (norm_nonneg _))
      _ = _ := by field_simp

theorem continuous_softKernelL2
    (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    (ds : List (Fin 3)) {k : ℝ} (hk : 0 ≤ k) (g : Ω → ℂ)
    (hg : Measurable g) (hbase : Integrable (fun y => ‖g y‖ ^ 2) ν) :
    Continuous (softKernelL2 momentum hm ds hk g hg hbase) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro xn hxn
  have hsoft : Integrable (fun y => ‖softBase momentum k g y‖ ^ 2) ν := by
    simpa only [one_mul] using softBase_weighted_integrable momentum hm k g (fun _ => 1)
      (by simpa only [one_mul] using hbase)
  have hsq : ∀ z y, ‖softDerivativeKernel momentum ds k z g y‖ ^ 2 ≤
      (k ^ ds.length) ^ 2 * ‖softBase momentum k g y‖ ^ 2 := by
    intro z y
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_softDerivativeKernel_le momentum ds hk z g y) 2
  apply GptLean.SymmetricLift.tendsto_toLp_two_of_dominated_sq
    (fun n => softDerivativeKernel_memLp momentum hm ds hk (xn n) g hg hbase)
    (softDerivativeKernel_memLp momentum hm ds hk x g hg hbase)
    (hsoft.const_mul ((k ^ ds.length) ^ 2))
    (fun n => Eventually.of_forall (hsq (xn n))) (Eventually.of_forall (hsq x))
  filter_upwards with y
  have hc : Continuous (fun z : FieldSpace => softDerivativeKernel momentum ds k z g y) := by
    unfold softDerivativeKernel fieldPhase
    fun_prop
  exact (hc.tendsto x).comp hxn

/-- Coordinate derivatives exist in the norm topology of one-photon L². -/
theorem softKernelL2_hasLineDerivAt
    (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    (ds : List (Fin 3)) (j : Fin 3) {k : ℝ} (hk : 0 ≤ k)
    (g : Ω → ℂ) (hg : Measurable g)
    (hbase : Integrable (fun y => ‖g y‖ ^ 2) ν) (x : FieldSpace) :
    HasLineDerivAt ℝ (softKernelL2 momentum hm ds hk g hg hbase)
      (softKernelL2 momentum hm (j :: ds) hk g hg hbase x)
      x (EuclideanSpace.single j 1) := by
  apply hasLineDerivAt_iff_tendsto_slope_zero.mpr
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro tn htn
  let f : ℕ → Ω → ℂ := fun n y => (tn n)⁻¹ •
    (softDerivativeKernel momentum ds k (x + tn n • EuclideanSpace.single j 1) g y -
      softDerivativeKernel momentum ds k x g y)
  let df : Ω → ℂ := softDerivativeKernel momentum (j :: ds) k x g
  have hf : ∀ n, MemLp (f n) 2 ν := fun n =>
    ((softDerivativeKernel_memLp momentum hm ds hk _ g hg hbase).sub
      (softDerivativeKernel_memLp momentum hm ds hk x g hg hbase)).const_smul ((tn n)⁻¹)
  have hdf : MemLp df 2 ν := softDerivativeKernel_memLp momentum hm (j :: ds) hk x g hg hbase
  have hsoft : Integrable (fun y => ‖softBase momentum k g y‖ ^ 2) ν := by
    simpa only [one_mul] using softBase_weighted_integrable momentum hm k g (fun _ => 1)
      (by simpa only [one_mul] using hbase)
  have hi : Integrable (fun y => (k ^ (ds.length + 1)) ^ 2 *
      ‖softBase momentum k g y‖ ^ 2) ν := hsoft.const_mul _
  have hlim := GptLean.SymmetricLift.tendsto_toLp_two_of_dominated_sq hf hdf hi
    (fun n => Eventually.of_forall (fun y => by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (softDerivativeKernel_slope_bound momentum ds j hk x g y (tn n)) 2))
    (Eventually.of_forall (fun y => by
      simpa only [mul_pow, List.length_cons] using pow_le_pow_left₀ (norm_nonneg _)
        (norm_softDerivativeKernel_le momentum (j :: ds) hk x g y) 2))
    (Eventually.of_forall (fun y =>
      (softDerivativeKernel_hasLineDerivAt momentum ds j k x g y).tendsto_slope_zero.comp htn))
  have heq : (fun n => (hf n).toLp (f n)) =
      (fun n => (tn n)⁻¹ •
        (softKernelL2 momentum hm ds hk g hg hbase (x + tn n • EuclideanSpace.single j 1) -
          softKernelL2 momentum hm ds hk g hg hbase x)) := by
    funext n
    change (((softDerivativeKernel_memLp momentum hm ds hk
      (x + tn n • EuclideanSpace.single j 1) g hg hbase).sub
        (softDerivativeKernel_memLp momentum hm ds hk x g hg hbase)).const_smul ((tn n)⁻¹)).toLp
          ((tn n)⁻¹ • (softDerivativeKernel momentum ds k
            (x + tn n • EuclideanSpace.single j 1) g - softDerivativeKernel momentum ds k x g)) = _
    rfl
  rw [heq] at hlim
  exact hlim

/-- The standard first-chaos map preserves the proved spatial derivative. -/
theorem firstChaos_soft_field_hasLineDerivAt
    {Q : Type*} [MeasurableSpace Q] {μ : Measure Q}
    (T : Lp ℂ 2 ν →L[ℝ] Lp ℝ 2 μ)
    (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    (ds : List (Fin 3)) (j : Fin 3) {k : ℝ} (hk : 0 ≤ k)
    (g : Ω → ℂ) (hg : Measurable g)
    (hbase : Integrable (fun y => ‖g y‖ ^ 2) ν) (x : FieldSpace) :
    HasLineDerivAt ℝ (fun z => T (softKernelL2 momentum hm ds hk g hg hbase z))
      (T (softKernelL2 momentum hm (j :: ds) hk g hg hbase x))
      x (EuclideanSpace.single j 1) := by
  exact T.hasFDerivAt.comp_hasDerivAt 0
    (softKernelL2_hasLineDerivAt momentum hm ds j hk g hg hbase x)

/-- The one-photon L² norm is uniformly controlled by the actual soft
kernel norm. In particular the bound is independent of the spatial point. -/
theorem norm_softKernelL2_le
    (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    (ds : List (Fin 3)) {k : ℝ} (hk : 0 ≤ k) (g : Ω → ℂ)
    (hg : Measurable g) (hbase : Integrable (fun y => ‖g y‖ ^ 2) ν) (x : FieldSpace) :
    ‖softKernelL2 momentum hm ds hk g hg hbase x‖ ≤
      k ^ ds.length * Real.sqrt (∫ y, ‖softBase momentum k g y‖ ^ 2 ∂ν) := by
  have hi : Integrable (fun y => ‖softBase momentum k g y‖ ^ 2) ν := by
    simpa using softBase_weighted_integrable momentum hm k g (fun _ => 1)
      (by simpa using hbase)
  have hmem := softDerivativeKernel_memLp momentum hm ds hk x g hg hbase
  have him := (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  have hb := (softDerivativeKernel_moment momentum ds hk x g (fun _ => 1)
    (fun _ => zero_le_one) (by simpa using hi)
    (by simpa only [one_mul] using him.1)).2
  simp only [one_mul] at hb
  have hn := GptLean.Repair.toL2_norm_sq hmem
  change ‖softKernelL2 momentum hm ds hk g hg hbase x‖ ^ 2 = _ at hn
  have hB : 0 ≤ ∫ y, ‖softBase momentum k g y‖ ^ 2 ∂ν :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hp : k ^ (2 * ds.length) = (k ^ ds.length) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hp, ← hn] at hb
  have hc : 0 ≤ k ^ ds.length * Real.sqrt (∫ y, ‖softBase momentum k g y‖ ^ 2 ∂ν) :=
    mul_nonneg (pow_nonneg hk _) (Real.sqrt_nonneg _)
  have he : (k ^ ds.length * Real.sqrt (∫ y, ‖softBase momentum k g y‖ ^ 2 ∂ν)) ^ 2 =
      (k ^ ds.length) ^ 2 * (∫ y, ‖softBase momentum k g y‖ ^ 2 ∂ν) := by
    rw [mul_pow, Real.sq_sqrt hB]
  nlinarith [norm_nonneg (softKernelL2 momentum hm ds hk g hg hbase x)]

/-- Every derivative order of the first-chaos field has local Bochner H¹
regularity, with the next Fourier kernels as its actual weak derivatives.
The integration-by-parts identity is a conclusion. -/
theorem firstChaos_soft_field_hasWeakH1Local
    {Q : Type*} [MeasurableSpace Q] {μ : Measure Q}
    (T : Lp ℂ 2 ν →L[ℝ] Lp ℝ 2 μ)
    (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    (ds : List (Fin 3)) {k : ℝ} (hk : 0 ≤ k)
    (g : Ω → ℂ) (hg : Measurable g)
    (hbase : Integrable (fun y => ‖g y‖ ^ 2) ν) :
    GptLean.SymmetricLift.HasWeakH1Local
      (fun z => T (softKernelL2 momentum hm ds hk g hg hbase z))
      (fun j z => T (softKernelL2 momentum hm (j :: ds) hk g hg hbase z)) := by
  apply GptLean.Repair.weakH1Local_of_continuous_bounded_lineDeriv
    (T.continuous.comp (continuous_softKernelL2 momentum hm ds hk g hg hbase))
    (fun j x => firstChaos_soft_field_hasLineDerivAt T momentum hm ds j hk g hg hbase x)
    (‖T‖ * (k ^ (ds.length + 1) * Real.sqrt (∫ y, ‖softBase momentum k g y‖ ^ 2 ∂ν)))
  intro j x
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (norm_softKernelL2_le momentum hm (j :: ds) hk g hg hbase x) (norm_nonneg _))

end GptLean.Gaussian
