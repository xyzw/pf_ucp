import GptLean.SymmetricLift.LiftH1Approximation
import GptLean.SymmetricLift.CompactTest

/-! Weak derivatives of the recursive lift obtained from source H1
approximations. All estimates and weak identities for the lifted sequence
are derived. The source approximation sequence and convergence of its
source derivatives are explicit hypotheses. -/

noncomputable section

namespace GptLean.SymmetricLift

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]

/-- The actual tensor lift passes to a strong H1 limit on each compact set.
The hypothesis about derivative convergence concerns the source tensors
only. The singular lifted term is handled by the proved pair-energy bound.
The global weak identity for each smooth lift is also proved, rather than
included among the approximation hypotheses. -/
theorem recursiveLift_weak_derivative_of_h1_approximation
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    (q : Fin N × Fin 3) {K : Set (Configuration N)} (hK : IsCompact K)
    {t : ℕ → EuclideanSpace ℝ (Fin 3) → V} {t₀ : EuclideanSpace ℝ (Fin 3) → V}
    (ht : ∀ n y, ‖t n y‖ ≤ 1) (ht₀ : ∀ y, ‖t₀ y‖ ≤ 1)
    (hT : ∀ n, AEStronglyMeasurable (configurationTensor B (t n) (N := N)) volume)
    (hT₀ : AEStronglyMeasurable (configurationTensor B t₀ (N := N)) volume)
    (hlim : ∀ᵐ x ∂volume.restrict K, Tendsto (fun n => configurationTensor B (t n) (N := N) x)
      atTop (𝓝 (configurationTensor B t₀ (N := N) x)))
    (hsmooth : ∀ n x, x ∈ distinctConfigurations N →
      DifferentiableAt ℝ (configurationTensor B (t n) (N := N)) x)
    (hdT : ∀ n, MemLp (fun x =>
      fderiv ℝ (configurationTensor B (t n) (N := N)) x (EuclideanSpace.single q 1))
        2 (volume.restrict K))
    {G : Configuration N → B.H N} (hG : MemLp G 2 (volume.restrict K))
    (hdlim : Tendsto (fun n => eLpNorm
      ((fun x => fderiv ℝ (configurationTensor B (t n) (N := N)) x (EuclideanSpace.single q 1)) - G)
        2 (volume.restrict K)) atTop (𝓝 0))
    {φ φ' : Configuration N → ℝ}
    (hφ : MemLp φ 2 (volume.restrict K)) (hφ' : MemLp φ' 2 (volume.restrict K))
    (hφzero : ∀ x, x ∉ K → φ x = 0) (hφ'zero : ∀ x, x ∉ K → φ' x = 0)
    (hφderiv : ∀ x, HasLineDerivAt ℝ φ (φ' x) x (EuclideanSpace.single q 1)) :
    (∫ x, φ x • recursiveLiftWeakDerivative B N q (configurationTensor B t₀ (N := N)) G x) =
      -(∫ x, φ' x • recursiveLiftField B N (configurationTensor B t₀ (N := N)) x) := by
  let : CompleteSpace (recursiveLiftCandidate B N).target := recursiveLiftCandidate_complete B N
  let T := fun n => configurationTensor B (t n) (N := N)
  let T₀ := configurationTensor B t₀ (N := N)
  let dT := fun n x => fderiv ℝ (T n) x (EuclideanSpace.single q 1)
  have hmT : ∀ n, MemLp (T n) 2 (volume.restrict K) := fun n =>
    configurationTensor_memLp_on_compact B M N hK (t n) (ht n) (hT n)
  have hmT₀ : MemLp T₀ 2 (volume.restrict K) :=
    configurationTensor_memLp_on_compact B M N hK t₀ ht₀ hT₀
  have hmF := fun n => recursiveLiftField_memLp_on B N K (hmT n)
  have hmF₀ := recursiveLiftField_memLp_on B N K hmT₀
  have hmA := fun n => recursiveLiftCorrection_memLp_on_compact B M N q hK (t n) (ht n) (hT n)
  have hmA₀ := recursiveLiftCorrection_memLp_on_compact B M N q hK t₀ ht₀ hT₀
  have hmB := fun n => recursiveLiftField_memLp_on B N K (hdT n)
  have hmB₀ := recursiveLiftField_memLp_on B N K hG
  have hF : Tendsto (fun n => eLpNorm
      (recursiveLiftField B N (T n) - recursiveLiftField B N T₀) 2 (volume.restrict K))
      atTop (𝓝 0) := by
    simpa only [recursiveLiftField_eLpNorm_sub] using
      configurationTensor_tendsto_eLpNorm_on_compact B M N hK ht ht₀ hT hT₀ hlim
  have hA := recursiveLiftCorrection_tendsto_eLpNorm_on_compact B M N q hK ht ht₀ hT hT₀ hlim
  have hB : Tendsto (fun n => eLpNorm
      (recursiveLiftField B N (dT n) - recursiveLiftField B N G) 2 (volume.restrict K))
      atTop (𝓝 0) := by
    simpa only [recursiveLiftField_eLpNorm_sub] using hdlim
  have hD := tendsto_eLpNorm_add_of_tendsto hmA hmB hmA₀ hmB₀ hA hB
  have hweak : ∀ n,
      (∫ x in K, φ x • recursiveLiftWeakDerivative B N q (T n) (dT n) x) =
      -(∫ x in K, φ' x • recursiveLiftField B N (T n) x) := by
    intro n
    rw [← integral_smul_eq_setIntegral _ hφzero, ← integral_smul_eq_setIntegral _ hφ'zero]
    exact recursiveLiftField_weak_coordinate_derivative B N q (hsmooth n) hφderiv
      (integrable_smul_of_memLp_on_support hφ' (hmF n) hφ'zero)
      (integrable_smul_of_memLp_on_support hφ ((hmA n).add (hmB n)) hφzero)
      (integrable_smul_of_memLp_on_support hφ (hmF n) hφzero)
  have hfinal := weak_derivative_identity_closed_eLpNorm hφ hφ'
    hmF (fun n => (hmA n).add (hmB n)) hmF₀ (hmA₀.add hmB₀) hF hD
    (Filter.Eventually.of_forall hweak)
  rw [integral_smul_eq_setIntegral _ hφzero, integral_smul_eq_setIntegral _ hφ'zero]
  exact hfinal

end GptLean.SymmetricLift
