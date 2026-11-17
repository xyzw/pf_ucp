import GptLean.SymmetricLift.SobolevLiftClosure
import GptLean.SymmetricLift.LocalMollification
import GptLean.SymmetricLift.TensorDerivativeApproximation
import GptLean.SymmetricLift.TensorApproximation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! The H1 local passage for arbitrary bounded weakly differentiable
one-particle fields. The source hypothesis uses local L2 membership and
integration by parts against compact smooth tests. Smooth approximants,
their derivative convergence and the lifted weak identities are constructed.
-/

noncomputable section

namespace GptLean.SymmetricLift

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology ContDiff

/-- The weak H1 local condition, expressed by local L2 fields and their
coordinate distributional identities. No approximation is part of this
definition. -/
structure HasWeakH1Local {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ I → E) (df : I → EuclideanSpace ℝ I → E) : Prop where
  function_memLp : ∀ K, IsCompact K → MemLp f 2 (volume.restrict K)
  derivative_memLp : ∀ i K, IsCompact K → MemLp (df i) 2 (volume.restrict K)
  weak : ∀ i (φ : EuclideanSpace ℝ I → ℝ),
    ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, φ x • df i x) = -(∫ x, (fderiv ℝ φ x (EuclideanSpace.single i 1)) • f x)

/-- Weak H1 local membership depends only on almost-everywhere classes. -/
theorem HasWeakH1Local.congr {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : EuclideanSpace ℝ I → E} {df df' : I → EuclideanSpace ℝ I → E}
    (h : HasWeakH1Local f df) (hf : f =ᵐ[volume] f') (hdf : ∀ i, df i =ᵐ[volume] df' i) :
    HasWeakH1Local f' df' := by
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    exact (h.function_memLp K hK).ae_eq (ae_restrict_le hf)
  · intro i K hK
    exact (h.derivative_memLp i K hK).ae_eq (ae_restrict_le (hdf i))
  · intro i φ hφ hφs
    calc
      (∫ x, φ x • df' i x) = ∫ x, φ x • df i x := by
        apply integral_congr_ae
        filter_upwards [hdf i] with x hx
        rw [hx]
      _ = -(∫ x, (fderiv ℝ φ x (EuclideanSpace.single i 1)) • f x) := h.weak i φ hφ hφs
      _ = -(∫ x, (fderiv ℝ φ x (EuclideanSpace.single i 1)) • f' x) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hf] with x hx
        rw [hx]

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [SeparableSpace V] [CompleteSpace V]

/-- The explicit gradient of the lifted field. -/
def recursiveLiftWeakGradient (B : TensorBackground V) (N : ℕ)
    (t : EuclideanSpace ℝ (Fin 3) → V) (g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V)
    (q : Fin N × Fin 3) : Configuration N → (recursiveLiftCandidate B N).target :=
  recursiveLiftWeakDerivative B N q (configurationTensor B t)
    (configurationTensorInsertion B q.1 t (g q.2))

/-- The local weak identity is derived from ordinary one-particle weak H1
data. The sequence used in the proof is the explicit shrinking mollifier. -/
theorem recursiveLift_weak_derivative_of_weak_h1
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    {t : EuclideanSpace ℝ (Fin 3) → V} {g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V}
    (h : HasWeakH1Local t g) (ht : ∀ y, ‖t y‖ ≤ 1)
    (q : Fin N × Fin 3) {K : Set (Configuration N)} (hK : IsCompact K)
    {φ φ' : Configuration N → ℝ}
    (hφ : MemLp φ 2 (volume.restrict K)) (hφ' : MemLp φ' 2 (volume.restrict K))
    (hφzero : ∀ x, x ∉ K → φ x = 0) (hφ'zero : ∀ x, x ∉ K → φ' x = 0)
    (hφderiv : ∀ x, HasLineDerivAt ℝ φ (φ' x) x (EuclideanSpace.single q 1)) :
    (∫ x, φ x • recursiveLiftWeakGradient B N t g q x) =
      -(∫ x, φ' x • recursiveLiftField B N (configurationTensor B t) x) := by
  have hti := localMemLp_two_locallyIntegrable h.function_memLp
  have hgi := localMemLp_two_locallyIntegrable (h.derivative_memLp q.2)
  let tn := boundedMollification t
  let gn := boundedMollification (g q.2)
  have htn (n : ℕ) : ContDiff ℝ ∞ (tn n) := boundedMollification_contDiff hti n
  have hgn (n : ℕ) : ContDiff ℝ ∞ (gn n) := boundedMollification_contDiff hgi n
  have htnm := fun n => (htn n).continuous.aestronglyMeasurable (μ := volume)
  have hgnm := fun n => (hgn n).continuous.aestronglyMeasurable (μ := volume)
  have htnb : ∀ n y, ‖tn n y‖ ≤ 1 :=
    boundedMollification_norm_le_one hti.aestronglyMeasurable ht
  have htlim := boundedMollification_ae_tendsto hti
  have hd (n : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
      fderiv ℝ (tn n) x (EuclideanSpace.single q.2 1) = gn n x := by
    exact ((htn n).differentiable (by simp) x).lineDeriv_eq_fderiv.symm.trans
      (boundedMollification_hasLineDerivAt hti (h.weak q.2) n x).lineDeriv
  have hDT (n : ℕ) :
      (fun x : Configuration N => fderiv ℝ (configurationTensor B (tn n)) x
        (EuclideanSpace.single q 1)) = configurationTensorInsertion B q.1 (tn n) (gn n) := by
    funext x
    rw [M.fderiv_configurationTensor_single (tn n) x q.1 q.2
      (fun i => (htn n).differentiable (by simp) (particle x i)), hd]
    rfl
  have hDTmem (n : ℕ) : MemLp
      (fun x : Configuration N => fderiv ℝ (configurationTensor B (tn n)) x
        (EuclideanSpace.single q 1)) 2 (volume.restrict K) := by
    rw [hDT n]
    exact M.memLp_configurationTensorInsertion q.1 (htnm n) (hgnm n) (htnb n)
      (fun C hC => boundedMollification_memLp_two_restrict hgi n hC) hK
  have hDTlim : Tendsto (fun n => eLpNorm
      ((fun x : Configuration N => fderiv ℝ (configurationTensor B (tn n)) x
        (EuclideanSpace.single q 1)) - configurationTensorInsertion B q.1 t (g q.2))
      2 (volume.restrict K)) atTop (𝓝 0) := by
    simp_rw [hDT]
    exact M.tendsto_eLpNorm_configurationTensorInsertion q.1 htnm hti.aestronglyMeasurable
      hgnm hgi.aestronglyMeasurable htnb ht (h.derivative_memLp q.2) htlim
      (fun C hC => boundedMollification_tendsto_eLpNorm_sub (h.derivative_memLp q.2) hC) hK
  exact recursiveLift_weak_derivative_of_h1_approximation B M N q hK htnb ht
    (fun n => M.aestronglyMeasurable_configurationTensor (N := N) (htnm n))
    (M.aestronglyMeasurable_configurationTensor (N := N) hti.aestronglyMeasurable)
    (ae_restrict_le (configurationTensor_ae_tendsto_of_ae B M N htlim))
    (fun n x _ => M.differentiableAt_configurationTensor (tn n) x
      (fun i => (htn n).differentiable (by simp) (particle x i)))
    hDTmem
    (M.memLp_configurationTensorInsertion q.1 hti.aestronglyMeasurable
      hgi.aestronglyMeasurable ht (h.derivative_memLp q.2) hK)
    hDTlim hφ hφ' hφzero hφ'zero hφderiv

/-- The constructed tensor lift has a locally square-integrable weak
gradient for every bounded weak H1 source field. No smooth approximation
sequence or source tensor derivative limit is assumed. -/
theorem recursiveLift_hasWeakH1Local
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    {t : EuclideanSpace ℝ (Fin 3) → V} {g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V}
    (h : HasWeakH1Local t g) (ht : ∀ y, ‖t y‖ ≤ 1) :
    HasWeakH1Local (recursiveLiftField B N (configurationTensor B t))
      (recursiveLiftWeakGradient B N t g) := by
  have hti := localMemLp_two_locallyIntegrable h.function_memLp
  have hT := M.aestronglyMeasurable_configurationTensor (N := N) hti.aestronglyMeasurable
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    exact recursiveLiftField_memLp_on B N K
      (configurationTensor_memLp_on_compact B M N hK t ht hT)
  · intro q K hK
    have hgi := localMemLp_two_locallyIntegrable (h.derivative_memLp q.2)
    exact (recursiveLiftCorrection_memLp_on_compact B M N q hK t ht hT).add
      (recursiveLiftField_memLp_on B N K
        (M.memLp_configurationTensorInsertion q.1 hti.aestronglyMeasurable
          hgi.aestronglyMeasurable ht (h.derivative_memLp q.2) hK))
  · intro q φ hφ hφs
    let φ' := fun x => fderiv ℝ φ x (EuclideanSpace.single q 1)
    have hφ' : Continuous φ' :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    exact recursiveLift_weak_derivative_of_weak_h1 B M N h ht q hφs
      ((hφ.continuous.memLp_of_hasCompactSupport hφs).restrict (tsupport φ))
      ((hφ'.memLp_of_hasCompactSupport (hφs.fderiv_apply ℝ _)).restrict (tsupport φ))
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
      (fun x hx => by simp [fderiv_of_notMem_tsupport ℝ hx])
      (fun x => ((hφ.differentiable (by simp)) x).hasFDerivAt.hasLineDerivAt _)

/-- The same result only requires the norm bound almost everywhere.
Changing exceptional one-particle values changes neither the configuration
tensor nor its insertion derivatives outside a null configuration set. -/
theorem recursiveLift_hasWeakH1Local_of_ae_bound
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    {t : EuclideanSpace ℝ (Fin 3) → V} {g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V}
    (h : HasWeakH1Local t g) (ht : ∀ᵐ y ∂volume, ‖t y‖ ≤ 1) :
    HasWeakH1Local (recursiveLiftField B N (configurationTensor B t))
      (recursiveLiftWeakGradient B N t g) := by
  classical
  let s := fun y => if ‖t y‖ ≤ 1 then t y else 0
  have hs : ∀ y, ‖s y‖ ≤ 1 := by
    intro y
    by_cases hy : ‖t y‖ ≤ 1
    · simpa only [s, ite_eq_left hy] using hy
    · simp only [s, ite_eq_right hy, norm_zero, zero_le_one]
  have hst : s =ᵐ[volume] t := ht.mono fun y hy => ite_eq_left hy
  have hsH := h.congr hst.symm (fun _ => Filter.EventuallyEq.rfl)
  have hparticles := ae_all_particles (N := N) hst
  have hT : ∀ᵐ x : Configuration N ∂volume,
      configurationTensor B s x = configurationTensor B t x := by
    filter_upwards [hparticles] with x hx
    unfold configurationTensor
    congr 1
    funext i
    exact hx i
  apply (recursiveLift_hasWeakH1Local B M N hsH hs).congr
  · filter_upwards [hT] with x hx
    simp only [recursiveLiftField, hx]
  · intro q
    filter_upwards [hparticles, hT] with x hx hTx
    have hG : configurationTensorInsertion B q.1 s (g q.2) x =
        configurationTensorInsertion B q.1 t (g q.2) x := by
      have hu : (fun i : Fin N => s (particle x i)) = (fun i => t (particle x i)) := funext hx
      simp only [configurationTensorInsertion, hu]
    simp only [recursiveLiftWeakGradient, recursiveLiftWeakDerivative, Pi.add_apply,
      recursiveLiftCorrection, recursiveLiftField, hTx, hG]

end GptLean.SymmetricLift
