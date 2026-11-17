import GptLean.SymmetricLift.BoundedTensorMetric
import GptLean.SymmetricLift.PairEnergyIntegrability
import GptLean.SymmetricLift.SmoothLiftWeakDerivative
import GptLean.SymmetricLift.L2Dominated
import GptLean.SymmetricLift.WeakDerivativeClosure
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-! The strong L2 passage for the constructed tensor lift.
The singular operator derivative is controlled by the proved pair metric
and the local integrability of inverse-square pair distances. Source
approximations and convergence of their source derivatives remain explicit.
-/

noncomputable section

namespace GptLean.SymmetricLift

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]

theorem configurationTensor_ae_tendsto_of_ae (B : TensorBackground V)
    (M : TensorMultilinearData B) (N : ℕ)
    {t : ℕ → EuclideanSpace ℝ (Fin 3) → V} {t₀ : EuclideanSpace ℝ (Fin 3) → V}
    (ht : ∀ᵐ y ∂volume, Tendsto (fun n => t n y) atTop (𝓝 (t₀ y))) :
    ∀ᵐ x : Configuration N ∂volume,
      Tendsto (fun n => configurationTensor B (t n) (N := N) x) atTop
        (𝓝 (configurationTensor B t₀ (N := N) x)) :=
  M.ae_configurationTensor_tendsto (ae_particle_tendsto ht)

/-- The operator-variation term in the candidate weak derivative. -/
def recursiveLiftCorrection (B : TensorBackground V) (N : ℕ) (q : Fin N × Fin 3)
    (T : Configuration N → B.H N) (x : Configuration N) :
    (recursiveLiftCandidate B N).target :=
  (fderiv ℝ (recursiveLiftCandidate B N).operator x (EuclideanSpace.single q 1)) (T x)

theorem recursiveLiftOperator_aestronglyMeasurable (B : TensorBackground V) (N : ℕ) :
    AEStronglyMeasurable (recursiveLiftCandidate B N).operator volume := by
  have h := (recursiveLiftCandidate_properties B N).smooth.continuousOn.aestronglyMeasurable
    (μ := volume) (distinctConfigurations_isOpen N).measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_distinctConfigurations N)] at h

theorem recursiveLiftOperator_fderiv_aestronglyMeasurable (B : TensorBackground V) (N : ℕ) :
    AEStronglyMeasurable (fderiv ℝ (recursiveLiftCandidate B N).operator) volume := by
  have hc := (recursiveLiftCandidate_properties B N).smooth.continuousOn_fderiv_of_isOpen
    (distinctConfigurations_isOpen N) (by simp)
  have h := hc.aestronglyMeasurable (μ := volume) (distinctConfigurations_isOpen N).measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_distinctConfigurations N)] at h

theorem recursiveLiftField_aestronglyMeasurable (B : TensorBackground V) (N : ℕ)
    {T : Configuration N → B.H N} (hT : AEStronglyMeasurable T volume) :
    AEStronglyMeasurable (recursiveLiftField B N T) volume := by
  exact (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := B.H N)
    (F := (recursiveLiftCandidate B N).target)).continuous.comp_aestronglyMeasurable₂
      (recursiveLiftOperator_aestronglyMeasurable B N) hT

theorem recursiveLiftCorrection_aestronglyMeasurable (B : TensorBackground V) (N : ℕ)
    (q : Fin N × Fin 3) {T : Configuration N → B.H N}
    (hT : AEStronglyMeasurable T volume) :
    AEStronglyMeasurable (recursiveLiftCorrection B N q T) volume := by
  exact (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := B.H N)
    (F := (recursiveLiftCandidate B N).target)).continuous.comp_aestronglyMeasurable₂
      ((recursiveLiftOperator_fderiv_aestronglyMeasurable B N).apply_continuousLinearMap
        (EuclideanSpace.single q 1)) hT

theorem recursiveLiftCorrection_sq_le (B : TensorBackground V) (M : TensorMultilinearData B)
    (N : ℕ) (q : Fin N × Fin 3) {x : Configuration N}
    (hx : x ∈ distinctConfigurations N) (t : EuclideanSpace ℝ (Fin 3) → V)
    (ht : ∀ y, ‖t y‖ ≤ 1) :
    ‖recursiveLiftCorrection B N q (configurationTensor B t (N := N)) x‖ ^ 2 ≤
      liftMetricConstant N * pairEnergy x := by
  calc
    _ ≤ operatorCoordinateMetric (recursiveLiftCandidate B N).operator x
        (configurationTensor B t (N := N) x) := by
      exact Finset.single_le_sum (fun i _ => sq_nonneg
        ‖(fderiv ℝ (recursiveLiftCandidate B N).operator x (EuclideanSpace.single i 1))
          (configurationTensor B t (N := N) x)‖) (Finset.mem_univ q)
    _ ≤ _ := recursiveLiftCandidate_pair_bound_of_norm_le_one B M N hx t ht

/-- The singular correction belongs to L2 on every compact configuration set. -/
theorem recursiveLiftCorrection_memLp_on_compact
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    (q : Fin N × Fin 3) {K : Set (Configuration N)} (hK : IsCompact K)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ ≤ 1)
    (hT : AEStronglyMeasurable (configurationTensor B t (N := N)) volume) :
    MemLp (recursiveLiftCorrection B N q (configurationTensor B t (N := N))) 2 (volume.restrict K) := by
  apply memLp_two_of_sq_norm_le
    (recursiveLiftCorrection_aestronglyMeasurable B N q hT).restrict
    (((locallyIntegrable_pairEnergy N).integrableOn_isCompact hK).const_mul (liftMetricConstant N))
  filter_upwards [ae_restrict_le (ae_distinctConfigurations N)] with x hx
  exact recursiveLiftCorrection_sq_le B M N q hx t ht

/-- Almost everywhere tensor convergence gives strong L2 convergence of
the singular correction on compact sets. No derivative convergence is
assumed for this term. -/
theorem recursiveLiftCorrection_tendsto_eLpNorm_on_compact
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    (q : Fin N × Fin 3) {K : Set (Configuration N)} (hK : IsCompact K)
    {t : ℕ → EuclideanSpace ℝ (Fin 3) → V} {t₀ : EuclideanSpace ℝ (Fin 3) → V}
    (ht : ∀ n y, ‖t n y‖ ≤ 1) (ht₀ : ∀ y, ‖t₀ y‖ ≤ 1)
    (hT : ∀ n, AEStronglyMeasurable (configurationTensor B (t n) (N := N)) volume)
    (hT₀ : AEStronglyMeasurable (configurationTensor B t₀ (N := N)) volume)
    (hlim : ∀ᵐ x ∂volume.restrict K, Tendsto (fun n => configurationTensor B (t n) (N := N) x)
      atTop (𝓝 (configurationTensor B t₀ (N := N) x))) :
    Tendsto (fun n => eLpNorm
      (recursiveLiftCorrection B N q (configurationTensor B (t n) (N := N)) -
        recursiveLiftCorrection B N q (configurationTensor B t₀ (N := N))) 2 (volume.restrict K))
      atTop (𝓝 0) := by
  apply tendsto_eLpNorm_two_of_dominated_sq
    (fun n => (recursiveLiftCorrection_aestronglyMeasurable B N q (hT n)).restrict)
    (recursiveLiftCorrection_aestronglyMeasurable B N q hT₀).restrict
    (((locallyIntegrable_pairEnergy N).integrableOn_isCompact hK).const_mul (liftMetricConstant N))
  · intro n
    filter_upwards [ae_restrict_le (ae_distinctConfigurations N)] with x hx
    exact recursiveLiftCorrection_sq_le B M N q hx (t n) (ht n)
  · filter_upwards [ae_restrict_le (ae_distinctConfigurations N)] with x hx
    exact recursiveLiftCorrection_sq_le B M N q hx t₀ ht₀
  · filter_upwards [hlim] with x hx
    exact ((fderiv ℝ (recursiveLiftCandidate B N).operator x
      (EuclideanSpace.single q 1)).continuous.tendsto _).comp hx

/-- The isometric part preserves the L2 error exactly, even across the
null collision set. -/
theorem recursiveLiftField_eLpNorm_sub (B : TensorBackground V) (N : ℕ)
    (T S : Configuration N → B.H N) (K : Set (Configuration N)) :
    eLpNorm (recursiveLiftField B N T - recursiveLiftField B N S) 2 (volume.restrict K) =
      eLpNorm (T - S) 2 (volume.restrict K) := by
  apply eLpNorm_congr_norm_ae
  filter_upwards [ae_restrict_le (ae_distinctConfigurations N)] with x hx
  simpa only [Pi.sub_apply, recursiveLiftField, ← map_sub] using
    (recursiveLiftCandidate_properties B N).norm x hx (T x - S x)

theorem recursiveLiftField_memLp_on (B : TensorBackground V) (N : ℕ)
    (K : Set (Configuration N)) {T : Configuration N → B.H N}
    (hT : MemLp T 2 (volume.restrict K)) :
    MemLp (recursiveLiftField B N T) 2 (volume.restrict K) := by
  apply hT.congr_norm
  · exact (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := B.H N)
      (F := (recursiveLiftCandidate B N).target)).continuous.comp_aestronglyMeasurable₂
        (recursiveLiftOperator_aestronglyMeasurable B N).restrict hT.aestronglyMeasurable
  · filter_upwards [ae_restrict_le (ae_distinctConfigurations N)] with x hx
    exact ((recursiveLiftCandidate_properties B N).norm x hx (T x)).symm

theorem configurationTensor_memLp_on_compact (B : TensorBackground V)
    (M : TensorMultilinearData B) (N : ℕ) {K : Set (Configuration N)} (hK : IsCompact K)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ ≤ 1)
    (hT : AEStronglyMeasurable (configurationTensor B t (N := N)) volume) :
    MemLp (configurationTensor B t (N := N)) 2 (volume.restrict K) := by
  apply memLp_two_of_sq_norm_le hT.restrict
    (integrableOn_const (C := (1 : ℝ)) hK.measure_lt_top.ne)
  apply ae_of_all
  intro x
  have h := M.pure_norm_le_one (fun i => t (particle x i)) (fun i => ht _)
  change ‖configurationTensor B t (N := N) x‖ ^ 2 ≤ 1
  change ‖configurationTensor B t (N := N) x‖ ≤ 1 at h
  nlinarith [norm_nonneg (configurationTensor B t (N := N) x)]

theorem configurationTensor_tendsto_eLpNorm_on_compact (B : TensorBackground V)
    (M : TensorMultilinearData B) (N : ℕ) {K : Set (Configuration N)} (hK : IsCompact K)
    {t : ℕ → EuclideanSpace ℝ (Fin 3) → V} {t₀ : EuclideanSpace ℝ (Fin 3) → V}
    (ht : ∀ n y, ‖t n y‖ ≤ 1) (ht₀ : ∀ y, ‖t₀ y‖ ≤ 1)
    (hT : ∀ n, AEStronglyMeasurable (configurationTensor B (t n) (N := N)) volume)
    (hT₀ : AEStronglyMeasurable (configurationTensor B t₀ (N := N)) volume)
    (hlim : ∀ᵐ x ∂volume.restrict K, Tendsto (fun n => configurationTensor B (t n) (N := N) x)
      atTop (𝓝 (configurationTensor B t₀ (N := N) x))) :
    Tendsto (fun n => eLpNorm (configurationTensor B (t n) (N := N) - configurationTensor B t₀ (N := N))
      2 (volume.restrict K)) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_two_of_dominated_sq (fun n => (hT n).restrict) hT₀.restrict
    (integrableOn_const (C := (1 : ℝ)) hK.measure_lt_top.ne) _ _ hlim
  · intro n
    apply ae_of_all
    intro x
    have h := M.pure_norm_le_one (fun i => t n (particle x i)) (fun i => ht n _)
    change ‖configurationTensor B (t n) (N := N) x‖ ^ 2 ≤ 1
    change ‖configurationTensor B (t n) (N := N) x‖ ≤ 1 at h
    nlinarith [norm_nonneg (configurationTensor B (t n) (N := N) x)]
  · apply ae_of_all
    intro x
    have h := M.pure_norm_le_one (fun i => t₀ (particle x i)) (fun i => ht₀ _)
    change ‖configurationTensor B t₀ (N := N) x‖ ^ 2 ≤ 1
    change ‖configurationTensor B t₀ (N := N) x‖ ≤ 1 at h
    nlinarith [norm_nonneg (configurationTensor B t₀ (N := N) x)]

/-- The derivative candidate for a source field with a prescribed weak
coordinate derivative. -/
def recursiveLiftWeakDerivative (B : TensorBackground V) (N : ℕ) (q : Fin N × Fin 3)
    (T G : Configuration N → B.H N) : Configuration N → (recursiveLiftCandidate B N).target :=
  recursiveLiftCorrection B N q T + recursiveLiftField B N G

theorem recursiveLiftWeakDerivative_norm_sq (B : TensorBackground V) (N : ℕ)
    (q : Fin N × Fin 3) (T G : Configuration N → B.H N)
    {x : Configuration N} (hx : x ∈ distinctConfigurations N) :
    ‖recursiveLiftWeakDerivative B N q T G x‖ ^ 2 = ‖G x‖ ^ 2 +
      ‖recursiveLiftCorrection B N q T x‖ ^ 2 := by
  have h := recursiveLiftCandidate_properties B N
  change ‖recursiveLiftCorrection B N q T x + recursiveLiftField B N G x‖ ^ 2 = _
  rw [add_comm]
  simpa only [recursiveLiftField, pow_two, h.norm x hx] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
      ((recursiveLiftCandidate B N).operator x (G x))
      (recursiveLiftCorrection B N q T x)
      (h.flat x hx (EuclideanSpace.single q 1) (G x) (T x))

end GptLean.SymmetricLift
