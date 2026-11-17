import GptLean.Repair.ScalarFormOperations
import GptLean.SymmetricLift.WeakDerivativeClosure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
The electronic H1 reference space is the closed graph of the actual weak
coordinate derivatives in L2. Closedness follows from continuity of the
compact smooth test integrals. Uniqueness follows from separation by those
same tests. No graph closure or completeness premise is supplied.
-/

noncomputable section

namespace GptLean.ElectronicH1Space

open MeasureTheory Filter GptLean.SymmetricLift GptLean.Repair
open scoped ENNReal Topology ContDiff

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev L2 (E I : Type*) [Fintype I] [NormedAddCommGroup E] :=
  Lp E 2 (volume : Measure (EuclideanSpace ℝ I))

/-- The actual weak derivative graph, viewed as a real submodule. -/
def weakGraph (E I : Type*) [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :
    Submodule ℝ (L2 E I × (I → L2 E I)) where
  carrier := {u | HasWeakH1Local (fun x => u.1 x) (fun i x => u.2 i x)}
  zero_mem' := by
    have hzero : HasWeakH1Local (fun _ : EuclideanSpace ℝ I => (0 : E))
        (fun _ _ => (0 : E)) := ⟨fun _ _ => MemLp.zero, fun _ _ _ => MemLp.zero,
          by intros; simp⟩
    exact hzero.congr (Lp.coeFn_zero E 2 volume).symm
      (fun _ => (Lp.coeFn_zero E 2 volume).symm)
  add_mem' := by
    intro u v hu hv
    exact (weakH1Local_add hu hv).congr (Lp.coeFn_add u.1 v.1).symm
      (fun i => (Lp.coeFn_add (u.2 i) (v.2 i)).symm)
  smul_mem' := by
    intro c u hu
    exact (weakH1Local_map (c • ContinuousLinearMap.id ℝ E) hu).congr
      (Lp.coeFn_smul c u.1).symm (fun i => (Lp.coeFn_smul c (u.2 i)).symm)

/-- The complete electronic reference space with its inherited graph norm. -/
abbrev H1 (E I : Type*) [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :=
  ↥(weakGraph E I)

def value : H1 E I →L[ℝ] L2 E I :=
  (ContinuousLinearMap.fst ℝ (L2 E I) (I → L2 E I)).comp (weakGraph E I).subtypeL

def gradient : H1 E I →L[ℝ] (I → L2 E I) :=
  (ContinuousLinearMap.snd ℝ (L2 E I) (I → L2 E I)).comp (weakGraph E I).subtypeL

def derivative (i : I) : H1 E I →L[ℝ] L2 E I :=
  (ContinuousLinearMap.proj i).comp gradient

@[simp] theorem value_apply (u : H1 E I) : value u = u.val.1 := rfl
@[simp] theorem gradient_apply (u : H1 E I) : gradient u = u.val.2 := rfl
@[simp] theorem derivative_apply (u : H1 E I) (i : I) : derivative i u = u.val.2 i := rfl

theorem weak (u : H1 E I) :
    HasWeakH1Local (fun x => value u x) (fun i x => derivative i u x) := u.property

/-- The weak derivative graph is closed in the product of the L2 spaces. -/
theorem isClosed_weakGraph :
    IsClosed (weakGraph E I : Set (L2 E I × (I → L2 E I))) := by
  apply IsSeqClosed.isClosed
  intro u v hu huv
  refine ⟨fun K _ => (Lp.memLp v.1).restrict K,
    fun i K _ => (Lp.memLp (v.2 i)).restrict K, ?_⟩
  intro i φ hφ hs
  have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  apply weak_derivative_identity_closed_l2
    (hφ.continuous.memLp_of_hasCompactSupport hs)
    (hdφ.memLp_of_hasCompactSupport (hs.fderiv_apply ℝ _))
    (continuous_fst.tendsto v |>.comp huv)
    (((continuous_apply i).comp continuous_snd).tendsto v |>.comp huv)
  exact Eventually.of_forall (fun n => (hu n).weak i φ hφ hs)

instance instCompleteSpace : CompleteSpace (H1 E I) :=
  isClosed_weakGraph.completeSpace_coe

theorem norm_eq_max (u : H1 E I) : ‖u‖ = max ‖value u‖ ‖gradient u‖ := rfl

theorem norm_value_le (u : H1 E I) : ‖value u‖ ≤ ‖u‖ :=
  _root_.norm_fst_le u.val

theorem norm_gradient_le (u : H1 E I) : ‖gradient u‖ ≤ ‖u‖ :=
  _root_.norm_snd_le u.val

theorem norm_derivative_le (u : H1 E I) (i : I) : ‖derivative i u‖ ≤ ‖u‖ :=
  (norm_le_pi_norm (gradient u) i).trans (norm_gradient_le u)

/-- The kinetic derivative energy uses the sum of coordinate L2 squares. -/
def derivativeEnergy (u : H1 E I) : ℝ := ∑ i, ‖derivative i u‖ ^ 2

theorem derivativeEnergy_nonneg (u : H1 E I) : 0 ≤ derivativeEnergy u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem derivativeEnergy_le (u : H1 E I) :
    derivativeEnergy u ≤ Fintype.card I * ‖u‖ ^ 2 := by
  calc
    derivativeEnergy u ≤ ∑ _i : I, ‖u‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_derivative_le u i) 2
    _ = _ := by simp

omit [DecidableEq I] [NormedSpace ℝ E] [CompleteSpace E] in
private theorem locallyIntegrable_L2 (f : L2 E I) :
    LocallyIntegrable (fun x => f x) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact MemLp.integrable (by norm_num) ((Lp.memLp f).restrict K)

/-- Compact smooth tests determine each weak derivative uniquely. -/
theorem derivative_eq_of_value_eq {u v : H1 E I} (h : value u = value v) (i : I) :
    derivative i u = derivative i v := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    (locallyIntegrable_L2 (derivative i u)) (locallyIntegrable_L2 (derivative i v))
  intro φ hφ hs
  rw [(weak u).weak i φ hφ hs, (weak v).weak i φ hφ hs, h]

theorem value_injective : Function.Injective (value : H1 E I → L2 E I) := by
  intro u v h
  apply Subtype.ext
  exact Prod.ext h (funext (derivative_eq_of_value_eq h))

theorem ext_ae {u v : H1 E I}
    (h : (value u : EuclideanSpace ℝ I → E) =ᵐ[volume] value v) : u = v :=
  value_injective (Lp.ext h)

/-- Package actual square-integrable functions and weak derivatives. -/
def ofFunctions (f : EuclideanSpace ℝ I → E) (df : I → EuclideanSpace ℝ I → E)
    (hf : MemLp f 2 volume) (hdf : ∀ i, MemLp (df i) 2 volume)
    (hw : HasWeakH1Local f df) : H1 E I :=
  ⟨(hf.toLp f, fun i => (hdf i).toLp (df i)),
    hw.congr hf.coeFn_toLp.symm (fun i => (hdf i).coeFn_toLp.symm)⟩

@[simp] theorem value_ofFunctions (f : EuclideanSpace ℝ I → E)
    (df : I → EuclideanSpace ℝ I → E) (hf : MemLp f 2 volume)
    (hdf : ∀ i, MemLp (df i) 2 volume) (hw : HasWeakH1Local f df) :
    value (ofFunctions f df hf hdf hw) = hf.toLp f := rfl

@[simp] theorem derivative_ofFunctions (f : EuclideanSpace ℝ I → E)
    (df : I → EuclideanSpace ℝ I → E) (hf : MemLp f 2 volume)
    (hdf : ∀ i, MemLp (df i) 2 volume) (hw : HasWeakH1Local f df) (i : I) :
    derivative i (ofFunctions f df hf hdf hw) = (hdf i).toLp (df i) := rfl

theorem value_ofFunctions_ae (f : EuclideanSpace ℝ I → E)
    (df : I → EuclideanSpace ℝ I → E) (hf : MemLp f 2 volume)
    (hdf : ∀ i, MemLp (df i) 2 volume) (hw : HasWeakH1Local f df) :
    (value (ofFunctions f df hf hdf hw) : EuclideanSpace ℝ I → E) =ᵐ[volume] f :=
  hf.coeFn_toLp

theorem derivative_ofFunctions_ae (f : EuclideanSpace ℝ I → E)
    (df : I → EuclideanSpace ℝ I → E) (hf : MemLp f 2 volume)
    (hdf : ∀ i, MemLp (df i) 2 volume) (hw : HasWeakH1Local f df) (i : I) :
    (derivative i (ofFunctions f df hf hdf hw) : EuclideanSpace ℝ I → E) =ᵐ[volume] df i :=
  (hdf i).coeFn_toLp

/-- Compactly supported smooth functions enter the actual weak graph. -/
def ofSmoothCompact (f : EuclideanSpace ℝ I → E)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) : H1 E I :=
  ofFunctions f (fun i x => fderiv ℝ f x (EuclideanSpace.single i 1))
    (hf.continuous.memLp_of_hasCompactSupport hs)
    (fun i => ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hs.fderiv_apply ℝ (EuclideanSpace.single i 1)))
    (weakH1Local_of_contDiff hf)

end GptLean.ElectronicH1Space
