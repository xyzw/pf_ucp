import GptLean.PhysicalRemovalKernels
import GptLean.PhysicalArticleCutoff

/-!
The sharp vacuum fluctuation coefficient of the article field. Summing
the three Cartesian components uses the unit norm of each polarization.
The two polarization channels cancel the factor one half in the kernel.
-/

noncomputable section
namespace GptLean.PhysicalCouplingKernelNorm

open MeasureTheory Gaussian PhysicalFock PhysicalPolarization
  PhotonLocalizationPhysicalKernels SymmetricLift
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000

variable (F : Frame) (χ : ArticleCutoff)

/-- The squared ultraviolet norm in the manuscript's Fourier convention. -/
def cutoffNormSq : ℝ := ∫ k, ‖χ.value k‖ ^ 2

theorem cutoffNormSq_nonneg : 0 ≤ cutoffNormSq χ :=
  integral_nonneg fun _ => sq_nonneg _

theorem base_sum_norm_sq (p : PhotonMode) :
    (∑ a : Fin 3, ‖base F χ a p‖ ^ 2) = χ.profileReal p := by
  have he : (∑ a : Fin 3, (F.epsilon p.1 p.2 a) ^ 2) = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (F.epsilon_norm p.1 p.2)
    rw [EuclideanSpace.norm_sq_eq] at h
    simpa only [Real.norm_eq_abs, sq_abs, one_pow] using h
  simp only [base, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_abs]
  rw [← Finset.sum_div, ← Finset.sum_mul, he, one_mul]
  rfl

theorem base_sum_integral :
    (∑ a : Fin 3, ∫ p, ‖base F χ a p‖ ^ 2 ∂photonMeasure) = cutoffNormSq χ := by
  rw [← integral_finsetSum Finset.univ (fun a _ => base_ultraviolet F χ a)]
  exact (integral_congr_ae (ae_of_all _ (base_sum_norm_sq F χ))).trans
    χ.integral_profileReal

theorem full_fst_norm_sq (N : ℕ) (q : Fin N × Fin 3) (x : Configuration N) :
    ‖(PhysicalRemovalKernels.full F χ N q x).val.1‖ ^ 2 =
      ∫ p, ‖base F χ q.2 p‖ ^ 2 ∂photonMeasure := by
  have h : (PhysicalRemovalKernels.full F χ N q x).val.1 =
      (formFactors F χ).fourierKernel (q.2, particle x q.1) := by
    change PhysicalOnePhotonFourier.fourier
      (PhysicalOnePhotonFourier.fourier.symm
        ((formFactors F χ).fourierKernel (q.2, particle x q.1))) = _
    exact PhysicalOnePhotonFourier.fourier.apply_symm_apply _
  rw [h]
  exact momentumKernelL2_norm_sq Prod.fst measurable_fst (base F χ q.2)
    (base_measurable F χ q.2) (base_ultraviolet F χ q.2) (particle x q.1)

theorem full_sum_norm_sq (N : ℕ) (x : Configuration N) :
    (∑ q : Fin N × Fin 3, ‖(PhysicalRemovalKernels.full F χ N q x).val.1‖ ^ 2) =
      (N : ℝ) * cutoffNormSq χ := by
  simp_rw [full_fst_norm_sq F χ]
  rw [Fintype.sum_prod_type]
  simp only [base_sum_integral F χ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

end GptLean.PhysicalCouplingKernelNorm
