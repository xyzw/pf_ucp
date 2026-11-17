import GptLean.PhysicalFockCutoffComposition
import GptLean.PhotonLocalizationLocalFormsOperators

/-!
An actual square-root splitting for the positive retained multiplier.
This supplies the square used to prove positivity of the physical Fock
vacuum compression, without an abstract second-quantization order premise.
-/

noncomputable section
namespace GptLean.PhysicalFock.CutoffRoot

open MeasureTheory PhotonLocalization PhotonLocalizationKernelCutoffs PhotonLocalizationFockChannel
open scoped ENNReal

variable {P E : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [MeasurableSpace P] [BorelSpace P] {μ : Measure P}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E]

omit [NormedAddCommGroup P] [InnerProductSpace ℝ P] [BorelSpace P]
  [InnerProductSpace ℝ E] [CompleteSpace E] [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
private theorem partition_norm (a b : P → ℝ)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (ha1 : ∀ᵐ x ∂μ, |a x| ≤ 1) (hb1 : ∀ᵐ x ∂μ, |b x| ≤ 1)
    (hpart : ∀ᵐ x ∂μ, a x ^ 2 + b x ^ 2 = 1) (u : Lp E 2 μ) :
    ‖realL2Multiplier a ha 1 ha1 u‖ ^ 2 + ‖realL2Multiplier b hb 1 hb1 u‖ ^ 2 = ‖u‖ ^ 2 := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral,
    PhotonKernelLocalization.l2_norm_sq_eq_integral,
    PhotonKernelLocalization.l2_norm_sq_eq_integral,
    ← integral_add
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))]
  apply integral_congr_ae
  filter_upwards [realL2Multiplier_apply a ha 1 ha1 u,
    realL2Multiplier_apply b hb 1 hb1 u, hpart] with x h₁ h₂ h₃
  rw [h₁, h₂]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← add_mul, h₃, one_mul]

def splitOfPartition (a b : P → ℝ)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (ha1 : ∀ᵐ x ∂μ, |a x| ≤ 1) (hb1 : ∀ᵐ x ∂μ, |b x| ≤ 1)
    (hpart : ∀ᵐ x ∂μ, a x ^ 2 + b x ^ 2 = 1) :
    Lp E 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp E 2 μ × Lp E 2 μ) where
  toLinearMap := (WithLp.linearEquiv 2 ℂ (Lp E 2 μ × Lp E 2 μ)).symm.toLinearMap.comp
    ((realL2Multiplier a ha 1 ha1).toLinearMap.prod (realL2Multiplier b hb 1 hb1).toLinearMap)
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact partition_norm a b ha hb ha1 hb1 hpart u

def rootRetained (r : ℝ) (x : P) : ℝ := Real.sqrt (retained r x)
def rootDiscarded (r : ℝ) (x : P) : ℝ := Real.sqrt (1 - retained r x)

theorem rootRetained_measurable (r : ℝ) : AEStronglyMeasurable (rootRetained (P := P) r) μ :=
  (Real.continuous_sqrt.comp (retained_smooth r).continuous).aestronglyMeasurable

theorem rootDiscarded_measurable (r : ℝ) : AEStronglyMeasurable (rootDiscarded (P := P) r) μ :=
  (Real.continuous_sqrt.comp (continuous_const.sub (retained_smooth r).continuous)).aestronglyMeasurable

omit [MeasurableSpace P] [BorelSpace P] in
theorem rootRetained_bound (r : ℝ) (x : P) : |rootRetained r x| ≤ 1 := by
  rw [rootRetained, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_one).mpr (retained_le_one r x)

omit [MeasurableSpace P] [BorelSpace P] in
theorem rootDiscarded_bound (r : ℝ) (x : P) : |rootDiscarded r x| ≤ 1 := by
  rw [rootDiscarded, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (Real.sqrt_le_one).mpr
  linarith [retained_nonneg r x]

omit [MeasurableSpace P] [BorelSpace P] in
theorem root_partition (r : ℝ) (x : P) : rootRetained r x ^ 2 + rootDiscarded r x ^ 2 = 1 := by
  rw [rootRetained, rootDiscarded, Real.sq_sqrt (retained_nonneg r x),
    Real.sq_sqrt (sub_nonneg.mpr (retained_le_one r x))]
  ring

def rootSplit (r : ℝ) : Lp E 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp E 2 μ × Lp E 2 μ) :=
  splitOfPartition (rootRetained r) (rootDiscarded r)
    (rootRetained_measurable r) (rootDiscarded_measurable r)
    (ae_of_all μ (rootRetained_bound r)) (ae_of_all μ (rootDiscarded_bound r))
    (ae_of_all μ (root_partition r))

omit [InnerProductSpace ℝ E] [CompleteSpace E] [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
theorem root_retained_apply (r : ℝ) (u : Lp E 2 μ) :
    retainedMap (rootSplit r) u =
      realL2Multiplier (rootRetained r) (rootRetained_measurable r) 1
        (ae_of_all μ (rootRetained_bound r)) u := rfl

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
theorem root_selfadjoint (r : ℝ) (u v : Lp E 2 μ) :
    inner ℂ (retainedMap (rootSplit r) u) v = inner ℂ u (retainedMap (rootSplit r) v) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (realL2Multiplier_selfadjoint (rootRetained r) (rootRetained_measurable r) 1
      (ae_of_all μ (rootRetained_bound r)))) u v

omit [CompleteSpace E] in
theorem root_square (r : ℝ) (u : Lp E 2 μ) :
    retainedMap (rootSplit r) (retainedMap (rootSplit r) u) = cutoffMap r u := by
  apply Lp.ext
  filter_upwards [realL2Multiplier_apply (rootRetained r) (rootRetained_measurable r) 1
      (ae_of_all μ (rootRetained_bound r)) (retainedMap (rootSplit r) u),
    realL2Multiplier_apply (rootRetained r) (rootRetained_measurable r) 1
      (ae_of_all μ (rootRetained_bound r)) u,
    PhotonKernelLocalization.l2Multiplier_apply_ae (retained r) (retained_measurable r)
      (ae_of_all μ (retained_abs_le_one r)) u] with x h₁ h₂ h₃
  have h₁' : retainedMap (rootSplit r) (retainedMap (rootSplit r) u) x =
      (rootRetained r x : ℂ) • retainedMap (rootSplit r) u x := by
    simpa only [root_retained_apply, Complex.coe_smul] using h₁
  have h₂' : retainedMap (rootSplit r) u x = (rootRetained r x : ℂ) • u x := by
    simpa only [root_retained_apply, Complex.coe_smul] using h₂
  have h₃' : retainedOperator r u x = (retained r x : ℂ) • u x :=
    (show retainedOperator r u x = retained r x • u x from h₃).trans
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)
  change retainedMap (rootSplit r) (retainedMap (rootSplit r) u) x = retainedOperator r u x
  rw [h₁', h₂', h₃', smul_smul]
  congr 1
  change (Real.sqrt (retained r x) : ℂ) * (Real.sqrt (retained r x) : ℂ) = (retained r x : ℂ)
  exact_mod_cast Real.mul_self_sqrt (retained_nonneg r x)

end GptLean.PhysicalFock.CutoffRoot
