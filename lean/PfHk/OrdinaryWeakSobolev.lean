import GptLean.ElectronicH1Reindex
import GptLean.PhysicalPairDerivativeBounds
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space

/-! The homogeneous Sobolev inequality on the actual weak H1 graph.
The smooth inequality is supplied by Mathlib and its passage to weak
functions uses the proved electronic smooth-core density. -/

noncomputable section
namespace PfHk.OrdinaryWeakSobolev

open MeasureTheory Filter GptLean GptLean.ElectronicH1Space
  GptLean.ElectronicH1Reindex GptLean.PhysicalPairDerivativeBounds
open scoped ENNReal NNReal Topology ContDiff

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Position (I : Type*) [Fintype I] := EuclideanSpace ℝ I

def constant (I : Type*) [Fintype I] : ℝ≥0 :=
  eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Position I)) 2

def derivativeSum (u : H1 ℝ I) : ℝ := ∑ i, ‖derivative i u‖

theorem derivativeSum_nonneg (u : H1 ℝ I) : 0 ≤ derivativeSum u :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem derivativeSum_continuous : Continuous (derivativeSum (I := I)) :=
  continuous_finsetSum Finset.univ fun i _ => (derivative i).continuous.norm

private theorem smooth_value_ae
    (f : Position I → ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    (value (ofSmoothCompact f hf hs) : Position I → ℝ) =ᵐ[volume] f :=
  (hf.continuous.memLp_of_hasCompactSupport hs).coeFn_toLp

private theorem smooth_derivative_ae
    (f : Position I → ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (i : I) :
    (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) =ᵐ[volume]
      derivative i (ofSmoothCompact f hf hs) :=
  (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hs.fderiv_apply ℝ (EuclideanSpace.single i 1))).coeFn_toLp.symm

attribute [local irreducible] value derivative weakGraph ofFunctions ofSmoothCompact

private theorem smooth_graph_bound {q : ℝ≥0}
    (hd : 0 < Fintype.card I)
    (hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (Fintype.card I : ℝ)⁻¹)
    (f : Position I → ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    eLpNorm (value (ofSmoothCompact f hf hs)) q volume ≤
      ENNReal.ofReal ((constant I : ℝ) * derivativeSum (ofSmoothCompact f hf hs)) := by
  have hrep : (value (ofSmoothCompact f hf hs) : Position I → ℝ) =ᵐ[volume] f :=
    smooth_value_ae f hf hs
  have hmath := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure (Position I))
    (hf.of_le (by simp) : ContDiff ℝ 1 f) hs (p := 2) (p' := q) (by norm_num)
    (by simpa only [finrank_euclideanSpace] using hd)
    (by simpa using hq)
  have hdcoord (i : I) :
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) =ᵐ[volume]
        derivative i (ofSmoothCompact f hf hs) :=
    smooth_derivative_ae f hf hs i
  have hb := eLpNorm_le_sum_coordinates (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (fderiv ℝ f) (fun i => (Lp.aestronglyMeasurable (derivative i (ofSmoothCompact f hf hs))).congr
      (hdcoord i).symm)
  have hsum : (∑ i, eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume) =
      ENNReal.ofReal (derivativeSum (ofSmoothCompact f hf hs)) := by
    rw [derivativeSum, ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [eLpNorm_congr_ae (hdcoord i), ← Lp.enorm_def, ← ofReal_norm]
  calc
    eLpNorm (value (ofSmoothCompact f hf hs)) q volume = eLpNorm f q volume := eLpNorm_congr_ae hrep
    _ ≤ (constant I : ℝ≥0∞) * eLpNorm (fderiv ℝ f) 2 volume := hmath
    _ ≤ (constant I : ℝ≥0∞) * ENNReal.ofReal (derivativeSum (ofSmoothCompact f hf hs)) :=
      mul_le_mul' le_rfl (hb.trans_eq hsum)
    _ = _ := by rw [ENNReal.ofReal_mul (constant I).coe_nonneg]; simp

theorem graph_bound {q : ℝ≥0} (hd : 0 < Fintype.card I)
    (hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (Fintype.card I : ℝ)⁻¹)
    (u : H1 ℝ I) :
    eLpNorm (value u) q volume ≤ ENNReal.ofReal ((constant I : ℝ) * derivativeSum u) := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp (dense_genericSmoothCore (E := ℝ) u)
  have hmeasure := tendstoInMeasure_of_tendsto_Lp ((value.continuous.tendsto u).comp hlim)
  have hb (n : ℕ) : eLpNorm (value (v n)) q volume ≤
      ENNReal.ofReal ((constant I : ℝ) * derivativeSum (v n)) := by
    obtain ⟨f, hf, hs, heq⟩ := hv n
    rw [heq]
    exact smooth_graph_bound hd hq f hf hs
  have hBlim : Tendsto (fun n => ENNReal.ofReal ((constant I : ℝ) * derivativeSum (v n)))
      atTop (𝓝 (ENNReal.ofReal ((constant I : ℝ) * derivativeSum u))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((derivativeSum_continuous.tendsto u).comp hlim).const_mul (constant I : ℝ))
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hB
  apply eLpNorm_le_of_tendstoInMeasure _ hmeasure (fun n => Lp.aestronglyMeasurable (value (v n)))
  filter_upwards [hBlim.eventually (eventually_lt_nhds hB)] with n hn
  exact (hb n).trans hn.le

private theorem sum_norm_sq (u : H1 ℝ I) :
    derivativeSum u ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, ‖derivative i u‖ ^ 2 := by
  simpa only [derivativeSum, one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : I => (1 : ℝ))
      (fun i => ‖derivative i u‖))

private theorem scalar_l2_square (f : Position I → ℝ) (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The ordinary homogeneous inequality for arbitrary real weak H1 functions.
The constant has no dependence on any coefficient or physical state. -/
theorem weak_bound {q : ℝ≥0} (hd : 0 < Fintype.card I)
    (hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (Fintype.card I : ℝ)⁻¹)
    (f : Position I → ℝ) (g : I → Position I → ℝ)
    (hw : SymmetricLift.HasWeakH1Local f g) (hf : MemLp f 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume) :
    MemLp f q volume ∧ (eLpNorm f q volume).toReal ^ 2 ≤
      ((constant I : ℝ) ^ 2 * Fintype.card I) * ∑ i, ∫ x, g i x ^ 2 := by
  let u := ofFunctions f g hf hg hw
  have hrep : (value u : Position I → ℝ) =ᵐ[volume] f := value_ofFunctions_ae f g hf hg hw
  have hb : eLpNorm f q volume ≤ ENNReal.ofReal ((constant I : ℝ) * derivativeSum u) :=
    (eLpNorm_congr_ae hrep).symm.le.trans (graph_bound hd hq u)
  have hmem : MemLp f q volume := ⟨hf.aestronglyMeasurable, hb.trans_lt ENNReal.ofReal_lt_top⟩
  have hreal : (eLpNorm f q volume).toReal ≤ (constant I : ℝ) * derivativeSum u :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg (constant I).coe_nonneg (derivativeSum_nonneg u)))
  have heq : (∑ i, ‖derivative i u‖ ^ 2) = ∑ i, ∫ x, g i x ^ 2 :=
    by
    apply Finset.sum_congr rfl
    intro i _
    change ‖derivative i (ofFunctions f g hf hg hw)‖ ^ 2 = _
    rw [derivative_ofFunctions]
    exact scalar_l2_square (g i) (hg i)
  refine ⟨hmem, ?_⟩
  calc
    _ ≤ ((constant I : ℝ) * derivativeSum u) ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 2
    _ = (constant I : ℝ) ^ 2 * derivativeSum u ^ 2 := mul_pow _ _ _
    _ ≤ (constant I : ℝ) ^ 2 * ((Fintype.card I : ℝ) * ∑ i, ‖derivative i u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_norm_sq u) (sq_nonneg _)
    _ = _ := by rw [heq]; ring

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

end PfHk.OrdinaryWeakSobolev
