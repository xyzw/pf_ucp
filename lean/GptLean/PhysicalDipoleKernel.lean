import GptLean.PhysicalDivergenceKernel
import GptLean.PhysicalRemovalKernels

/-!
The spatially scaled article kernels and their actual Fock fields.
Continuity of the weighted Fourier kernels and dominated convergence prove
strong field convergence for every fixed vector in the radiation form
domain. The scale is allowed to be any real number, including zero.
-/

noncomputable section

namespace GptLean.PhysicalDipoleKernel

open MeasureTheory Filter Topology PhysicalFock PhysicalPolarization SymmetricLift
  Gaussian PhysicalDivergenceKernel
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable (F : Frame) (χ : ArticleCutoff) (N : ℕ)

/-- The article kernel evaluated at the scaled electronic position. -/
def scaled (ε : ℝ) (i : Fin N × Fin 3) (x : Configuration N) : WeightedPhotonKernel :=
  kernel F χ (i.2, ε • particle x i.1)

theorem scaled_measurable (ε : ℝ) (i : Fin N × Fin 3) :
    AEStronglyMeasurable (scaled F χ N ε i) volume := by
  have hp : Continuous (fun x : Configuration N => ε • particle x i.1) :=
    (particleLinear i.1).continuous_of_finiteDimensional.const_smul ε
  exact ((continuous_kernel F χ i.2).comp hp).aestronglyMeasurable

theorem scaled_bound_pointwise (ε : ℝ) (i : Fin N × Fin 3) (x : Configuration N) :
    ‖scaled F χ N ε i x‖ ≤ PhysicalRemovalKernels.bound F χ :=
  PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl
    (LinearIsometryEquiv.refl ℝ _) (i.2, ε • particle x i.1)

theorem scaled_bound (ε : ℝ) (i : Fin N × Fin 3) :
    ∀ᵐ x ∂volume, ‖scaled F χ N ε i x‖ ≤ PhysicalRemovalKernels.bound F χ :=
  ae_of_all _ (scaled_bound_pointwise F χ N ε i)

theorem scaled_one : scaled F χ N 1 = PhysicalRemovalKernels.full F χ N := by
  funext i x
  simp only [scaled, one_smul]
  rfl

theorem scaled_zero (i : Fin N × Fin 3) (x : Configuration N) :
    scaled F χ N 0 i x = kernel F χ (i.2, 0) := by
  simp only [scaled, zero_smul]

theorem continuous_scaled (i : Fin N × Fin 3) (x : Configuration N) :
    Continuous (fun ε : ℝ => scaled F χ N ε i x) :=
  (continuous_kernel F χ i.2).comp (continuous_id.smul continuous_const)

variable (C : CanonicalSectorCCR photonMeasure)

/-- The operator is the previously constructed spatial Fock field. -/
def field (ε : ℝ) (i : Fin N × Fin 3) :
    SpatialRadiationGraph (volume : Measure (Configuration N)) →L[ℂ]
      SpatialPhotonSpace (volume : Measure (Configuration N)) :=
  spatialField volume C (scaled F χ N ε i) (scaled_measurable F χ N ε i)
    (PhysicalRemovalKernels.bound F χ) (scaled_bound F χ N ε i)

theorem field_ae (ε : ℝ) (i : Fin N × Fin 3)
    (u : SpatialRadiationGraph (volume : Measure (Configuration N))) :
    field F χ N C ε i u =ᵐ[volume]
      fun x => kernelField C (scaled F χ N ε i x) (u x) :=
  spatialField_ae volume C _ _ _ _ u

private theorem field_bound (ε : ℝ) (i : Fin N × Fin 3)
    (u : SpatialRadiationGraph (volume : Measure (Configuration N))) :
    ∀ᵐ x ∂volume, ‖field F χ N C ε i u x‖ ≤
      ((2 * ‖radiationGraphDerivative‖ + ‖radiationGraphInclusion‖) *
        PhysicalRemovalKernels.bound F χ) * ‖u x‖ := by
  filter_upwards [field_ae F χ N C ε i u] with x hx
  rw [hx]
  apply ((kernelField C (scaled F χ N ε i x)).le_opNorm (u x)).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (kernelField_opNorm_le C _).trans
    (mul_le_mul_of_nonneg_left (scaled_bound_pointwise F χ N ε i x) (by positivity))

/-- Strong convergence on a fixed radiation-domain vector follows from an
integrable square bound. There is no spatial support assumption. -/
theorem field_tendsto (ε : ℕ → ℝ) {ε₀ : ℝ} (hε : Tendsto ε atTop (𝓝 ε₀))
    (i : Fin N × Fin 3)
    (u : SpatialRadiationGraph (volume : Measure (Configuration N))) :
    Tendsto (fun n => field F χ N C (ε n) i u) atTop (𝓝 (field F χ N C ε₀ i u)) := by
  let A := (2 * ‖radiationGraphDerivative‖ + ‖radiationGraphInclusion‖) *
    PhysicalRemovalKernels.bound F χ
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  apply SymmetricLift.tendsto_eLpNorm_two_of_dominated_sq
    (b := fun x => A ^ 2 * ‖u x‖ ^ 2)
    (fun n => Lp.aestronglyMeasurable (field F χ N C (ε n) i u))
    (Lp.aestronglyMeasurable (field F χ N C ε₀ i u))
    (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp
      (Lp.memLp u)).const_mul (A ^ 2))
  · intro n
    filter_upwards [field_bound F χ N C (ε n) i u] with x hx
    simpa only [A, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hx 2
  · filter_upwards [field_bound F χ N C ε₀ i u] with x hx
    simpa only [A, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hx 2
  · filter_upwards [ae_all_iff.mpr (fun n => field_ae F χ N C (ε n) i u),
      field_ae F χ N C ε₀ i u] with x hx hx₀
    simp only [hx, hx₀]
    exact (((kernelField_continuous C).comp (continuous_scaled F χ N i x)).clm_apply
      continuous_const).tendsto ε₀ |>.comp hε

/-- Full real-parameter field convergence, including the dipole endpoint. -/
theorem continuous_spatialField (i : Fin N × Fin 3)
    (u : SpatialRadiationGraph (volume : Measure (Configuration N))) :
    Continuous (fun ε : ℝ => field F χ N C ε i u) := by
  apply continuous_iff_continuousAt.mpr
  intro ε₀
  exact tendsto_nhds_iff_seq_tendsto.mpr
    (fun ε hε => field_tendsto F χ N C ε hε i u)

end GptLean.PhysicalDipoleKernel
