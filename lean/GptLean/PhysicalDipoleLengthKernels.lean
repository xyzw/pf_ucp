import GptLean.PhysicalDipoleGaussian
import GptLean.PhysicalDipoleMoment

/-! The additional ultraviolet moment, actual dipole displacement, and its
real positive semidefinite polarization matrix. -/

noncomputable section
namespace GptLean.PhysicalDipoleLengthKernels

open MeasureTheory Filter Topology PhysicalFock PhysicalPolarization
  PhysicalDipoleGaussian PhysicalDipoleMoment Gaussian PhotonLocalizationPhysicalKernels
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

/-- The article's additional ultraviolet assumption, literally √ωχ ∈ L². -/
def UVCondition (χ : ArticleCutoff) : Prop :=
  MemLp (fun k => (Real.sqrt ‖k‖ : ℂ) * χ.value k) 2 volume

theorem sqrt_mul_norm_sq (k : FieldSpace) (z : ℂ) :
    ‖(Real.sqrt ‖k‖ : ℂ) * z‖ ^ 2 = ‖k‖ * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (norm_nonneg _)]

theorem uv_iff_integrable (χ : ArticleCutoff) :
    UVCondition χ ↔ Integrable (fun k => ‖k‖ * ‖χ.value k‖ ^ 2) volume := by
  have hm : AEStronglyMeasurable (fun k : FieldSpace => (Real.sqrt ‖k‖ : ℂ) * χ.value k) volume :=
    ((Complex.measurable_ofReal.comp measurable_norm.sqrt).mul χ.measurable).aestronglyMeasurable
  simpa only [UVCondition, sqrt_mul_norm_sq] using (memLp_two_iff_integrable_sq_norm hm)

variable (F : Frame) (χ : ArticleCutoff) (hUV : UVCondition χ)

def sqrtBase (i : Fin 3) (p : PhotonMode) : ℂ :=
  (Real.sqrt ‖p.1‖ : ℂ) * base F χ i p

theorem sqrtBase_measurable (i : Fin 3) : Measurable (sqrtBase F χ i) :=
  (Complex.measurable_ofReal.comp measurable_fst.norm.sqrt).mul (base_measurable F χ i)

include hUV in
theorem sqrtBase_memLp (i : Fin 3) : MemLp (sqrtBase F χ i) 2 photonMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (sqrtBase_measurable F χ i).aestronglyMeasurable).mpr
  have h := ((Measure.measurePreserving_neg volume).integrable_comp_of_integrable
    ((uv_iff_integrable χ).mp hUV)).comp_fst (Measure.count : Measure (Fin 2))
  simp only [Function.comp_def, norm_neg] at h
  apply h.mono' ((sqrtBase_measurable F χ i).norm.pow_const 2).aestronglyMeasurable
  refine ae_of_all _ fun p => ?_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change ‖(Real.sqrt ‖p.1‖ : ℂ) * base F χ i p‖ ^ 2 ≤ _
  rw [sqrt_mul_norm_sq]
  exact mul_le_mul_of_nonneg_left (base_norm_bound F χ i p) (norm_nonneg _)

/-- The actual L² vector √ω Gᵢ(0). -/
def weightedKernel (i : Fin 3) : Lp ℂ 2 photonMeasure :=
  (sqrtBase_memLp F χ hUV i).toLp (sqrtBase F χ i)

theorem weightedKernel_ae (i : Fin 3) :
    weightedKernel F χ hUV i =ᵐ[photonMeasure] sqrtBase F χ i := MemLp.coeFn_toLp _

theorem constantLabel_ae (i : Fin 3) :
    (((constantLabel F χ i : OnePhotonTop) : Lp ℂ 2 photonMeasure) : PhotonMode → ℂ)
      =ᵐ[photonMeasure] base F χ i := by
  have h : (((constantLabel F χ i : OnePhotonTop) : Lp ℂ 2 photonMeasure) : PhotonMode → ℂ)
      =ᵐ[photonMeasure] momentumKernel Prod.fst (base F χ i) 0 :=
    momentumKernelL2_ae Prod.fst measurable_fst (base F χ i)
      (base_measurable F χ i) (base_ultraviolet F χ i) (0 : FieldSpace)
  filter_upwards [h] with p hp
  simpa [momentumKernel, fieldPhase] using hp

theorem weightedKernel_relation (i : Fin 3) :
    ∀ᵐ p ∂photonMeasure, weightedKernel F χ hUV i p = (Real.sqrt ‖p.1‖ : ℂ) *
      (((constantLabel F χ i : OnePhotonTop) : Lp ℂ 2 photonMeasure) p) := by
  filter_upwards [weightedKernel_ae F χ hUV i, constantLabel_ae F χ i] with p hp hq
  exact hp.trans (congrArg ((Real.sqrt ‖p.1‖ : ℂ) * ·) hq.symm)

/-- The displacement before multiplication by i. -/
def displacement {N : ℕ} (e : ℝ) (x : SymmetricLift.Configuration N) : Lp ℂ 2 photonMeasure :=
  ∑ j : Fin N × Fin 3, ((e * x j : ℝ) : ℂ) •
    ((constantLabel F χ j.2 : OnePhotonTop) : Lp ℂ 2 photonMeasure)

/-- Its square-root-frequency weighted vector. -/
def weightedDisplacement {N : ℕ} (e : ℝ) (x : SymmetricLift.Configuration N) : Lp ℂ 2 photonMeasure :=
  ∑ j : Fin N × Fin 3, ((e * x j : ℝ) : ℂ) • weightedKernel F χ hUV j.2

private theorem weighted_relation_sum {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (f y : ι → Lp ℂ 2 photonMeasure)
    (h : ∀ i, ∀ᵐ p ∂photonMeasure, y i p = (Real.sqrt ‖p.1‖ : ℂ) * f i p) :
    ∀ᵐ p ∂photonMeasure, (∑ i, a i • y i) p =
      (Real.sqrt ‖p.1‖ : ℂ) * (∑ i, a i • f i) p := by
  have hf := Lp.coeFn_finsetSum Finset.univ (fun i => a i • f i)
  have hy := Lp.coeFn_finsetSum Finset.univ (fun i => a i • y i)
  have hs : ∀ᵐ p ∂photonMeasure, ∀ i, (a i • y i) p =
      (Real.sqrt ‖p.1‖ : ℂ) * (a i • f i) p := by
    rw [ae_all_iff]
    intro i
    filter_upwards [h i, Lp.coeFn_smul (a i) (f i), Lp.coeFn_smul (a i) (y i)] with p hp hfp hyp
    simp only [Pi.smul_apply, smul_eq_mul] at hfp hyp
    rw [hyp, hfp, hp]
    ring
  filter_upwards [hf, hy, hs] with p hfp hyp hp
  simp only [Finset.sum_apply] at hfp hyp
  rw [hyp, hfp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hp i

theorem weightedDisplacement_relation {N : ℕ} (e : ℝ) (x : SymmetricLift.Configuration N) :
    ∀ᵐ p ∂photonMeasure, weightedDisplacement F χ hUV e x p =
      (Real.sqrt ‖p.1‖ : ℂ) * displacement F χ e x p :=
  weighted_relation_sum _ _ _ fun j => weightedKernel_relation F χ hUV j.2

theorem imaginary_displacement_relation {N : ℕ} (e : ℝ) (x : SymmetricLift.Configuration N) :
    ∀ᵐ p ∂photonMeasure, (Complex.I • weightedDisplacement F χ hUV e x) p =
      (Real.sqrt ‖p.1‖ : ℂ) * (Complex.I • displacement F χ e x) p := by
  filter_upwards [weightedDisplacement_relation F χ hUV e x,
    Lp.coeFn_smul Complex.I (weightedDisplacement F χ hUV e x),
    Lp.coeFn_smul Complex.I (displacement F χ e x)] with p hp h1 h2
  simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
  rw [h1, h2, hp]
  ring

/-- The matrix in the article is the real Gram matrix of √ω Gᵢ(0). -/
def polarizationMatrix (i j : Fin 3) : ℝ :=
  (⟪weightedKernel F χ hUV i, weightedKernel F χ hUV j⟫_ℂ).re

theorem polarizationMatrix_symmetric (i j : Fin 3) :
    polarizationMatrix F χ hUV i j = polarizationMatrix F χ hUV j i := by
  unfold polarizationMatrix
  exact inner_re_symm (𝕜 := ℂ) (weightedKernel F χ hUV i) (weightedKernel F χ hUV j)

private theorem gram_sum (g : Fin 3 → Lp ℂ 2 photonMeasure) (r : Fin 3 → ℝ) :
    ‖∑ i, (r i : ℂ) • g i‖ ^ 2 =
      ∑ i, ∑ j, r i * (⟪g i, g j⟫_ℂ).re * r j := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (⟪∑ i, (r i : ℂ) • g i, ∑ i, (r i : ℂ) • g i⟫_ℂ).re = _
  rw [sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem polarizationMatrix_nonnegative (r : Fin 3 → ℝ) :
    0 ≤ ∑ i, ∑ j, r i * polarizationMatrix F χ hUV i j * r j := by
  change 0 ≤ ∑ i, ∑ j, r i * (⟪weightedKernel F χ hUV i, weightedKernel F χ hUV j⟫_ℂ).re * r j
  rw [← gram_sum]
  exact sq_nonneg _



theorem totalPosition_apply {N : ℕ} (x : SymmetricLift.Configuration N) (μ : Fin 3) :
    totalPosition x μ = ∑ n : Fin N, x (n, μ) := by
  simp only [totalPosition, WithLp.ofLp_sum, Finset.sum_apply, SymmetricLift.particle,
    WithLp.ofLp_toLp]

private theorem grouped_sum {N : ℕ} (g : Fin 3 → Lp ℂ 2 photonMeasure)
    (e : ℝ) (x : SymmetricLift.Configuration N) :
    (∑ j : Fin N × Fin 3, ((e * x j : ℝ) : ℂ) • g j.2) =
      ∑ μ : Fin 3, ((e * totalPosition x μ : ℝ) : ℂ) • g μ := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  rw [totalPosition_apply, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_smul]

theorem displacement_grouped {N : ℕ} (e : ℝ) (x : SymmetricLift.Configuration N) :
    displacement F χ e x = ∑ μ : Fin 3, ((e * totalPosition x μ : ℝ) : ℂ) •
      ((constantLabel F χ μ : OnePhotonTop) : Lp ℂ 2 photonMeasure) :=
  grouped_sum (fun μ => ((constantLabel F χ μ : OnePhotonTop) : Lp ℂ 2 photonMeasure)) e x

theorem weightedDisplacement_grouped {N : ℕ} (e : ℝ) (x : SymmetricLift.Configuration N) :
    weightedDisplacement F χ hUV e x = ∑ μ : Fin 3, ((e * totalPosition x μ : ℝ) : ℂ) •
      weightedKernel F χ hUV μ := grouped_sum (weightedKernel F χ hUV) e x

theorem displacement_continuous {N : ℕ} (e : ℝ) :
    Continuous (displacement F χ (N := N) e) := by
  unfold displacement
  apply continuous_finsetSum
  intro j _
  exact (Complex.continuous_ofReal.comp
    (continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) j))).smul continuous_const

theorem weightedDisplacement_continuous {N : ℕ} (e : ℝ) :
    Continuous (weightedDisplacement F χ hUV (N := N) e) := by
  unfold weightedDisplacement
  apply continuous_finsetSum
  intro j _
  exact (Complex.continuous_ofReal.comp
    (continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) j))).smul continuous_const

/-- A finite constant bounding the polarization quadratic form. -/
def polarizationBound : ℝ := (∑ μ : Fin 3, ‖weightedKernel F χ hUV μ‖) ^ 2

theorem weightedDisplacement_norm_sq_le {N : ℕ} (e : ℝ) (x : SymmetricLift.Configuration N) :
    ‖weightedDisplacement F χ hUV e x‖ ^ 2 ≤
      e ^ 2 * polarizationBound F χ hUV * ‖totalPosition x‖ ^ 2 := by
  have hn : ‖weightedDisplacement F χ hUV e x‖ ≤
      |e| * (∑ μ : Fin 3, ‖weightedKernel F χ hUV μ‖) * ‖totalPosition x‖ := by
    rw [weightedDisplacement_grouped]
    calc _ ≤ ∑ μ : Fin 3, ‖((e * totalPosition x μ : ℝ) : ℂ) • weightedKernel F χ hUV μ‖ := norm_sum_le _ _
      _ ≤ ∑ μ : Fin 3, |e| * ‖totalPosition x‖ * ‖weightedKernel F χ hUV μ‖ := by
        apply Finset.sum_le_sum
        intro μ _
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (totalPosition x) μ) (abs_nonneg _))
          (norm_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  simpa only [mul_pow, sq_abs, polarizationBound] using hsq

theorem weightedDisplacement_norm_sq {N : ℕ} (e : ℝ) (x : SymmetricLift.Configuration N) :
    ‖weightedDisplacement F χ hUV e x‖ ^ 2 =
      e ^ 2 * ∑ μ : Fin 3, ∑ ν : Fin 3,
        totalPosition x μ * polarizationMatrix F χ hUV μ ν * totalPosition x ν := by
  rw [weightedDisplacement_grouped, gram_sum]
  simp only [Finset.mul_sum, polarizationMatrix]
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  ring

end GptLean.PhysicalDipoleLengthKernels
