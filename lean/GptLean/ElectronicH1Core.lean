import GptLean.ElectronicH1Cutoff
import GptLean.SymmetricLift.L2Mollification
import GptLean.SymmetricLift.BoundedMollification

/-!
Smooth compactly supported functions are dense in the actual electronic H1
space. First expanding smooth cutoffs converge in the graph norm. Each
compact field and all of its weak derivatives are then mollified together.
The approximants and both convergence passages are constructed here.
-/

noncomputable section

namespace GptLean.ElectronicH1Core

open MeasureTheory Filter GptLean.SymmetricLift GptLean.ElectronicH1Space
open scoped ENNReal Topology ContDiff Convolution

variable {d : ℕ} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def smoothCore (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (d : ℕ) : Set (H1 E (Fin d)) :=
  {u | ∃ (f : EuclideanSpace ℝ (Fin d) → E) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f), u = ofSmoothCompact f hf hs}

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem integrable_of_memLp_compact {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : MemLp f 2 volume) (hs : HasCompactSupport f) : Integrable f volume := by
  let : IsFiniteMeasure (volume.restrict (tsupport f)) :=
    isFiniteMeasure_restrict.mpr hs.measure_lt_top.ne
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
  exact MemLp.integrable (by norm_num) (hf.restrict (tsupport f))

private theorem mollification_tendsto_global {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : MemLp f 2 volume) (hs : HasCompactSupport f) :
    Tendsto (fun n => eLpNorm (boundedMollification f n - f) 2 volume) atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_convolution_sub
    (fun n => (approximationBump d n).integrable_normed (μ := volume))
    (Eventually.of_forall fun n => (approximationBump d n).nonneg_normed)
    (Eventually.of_forall fun n => (approximationBump d n).integral_normed)
    (ContDiffBump.tendsto_support_normed_smallSets (approximationBump_rOut_tendsto d))
    (integrable_of_memLp_compact hf hs) hf
  simpa only [boundedMollification, smoothMollify, convolution_flip] using h

/-- Compact H1 fields lie in the closure of the concrete smooth core. -/
theorem mem_closure_smoothCore_of_compact
    (f : EuclideanSpace ℝ (Fin d) → E) (df : Fin d → EuclideanSpace ℝ (Fin d) → E)
    (hf : MemLp f 2 volume) (hdf : ∀ i, MemLp (df i) 2 volume)
    (hw : HasWeakH1Local f df) (hs : HasCompactSupport f)
    (hds : ∀ i, HasCompactSupport (df i)) :
    ofFunctions f df hf hdf hw ∈ closure (smoothCore E d) := by
  have hlocal := localMemLp_two_locallyIntegrable hw.function_memLp
  let fn := boundedMollification f
  have hfn (n : ℕ) : ContDiff ℝ ∞ (fn n) := boundedMollification_contDiff hlocal n
  have hsn (n : ℕ) : HasCompactSupport (fn n) := by
    exact hs.convolution
      ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip)
      (approximationBump d n).hasCompactSupport_normed
  let un (n : ℕ) : H1 E (Fin d) := ofSmoothCompact (fn n) (hfn n) (hsn n)
  have hdn (n : ℕ) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
      fderiv ℝ (fn n) x (EuclideanSpace.single i 1) = boundedMollification (df i) n x := by
    exact ((hfn n).differentiable (by simp) x).lineDeriv_eq_fderiv.symm.trans
      (boundedMollification_hasLineDerivAt hlocal (hw.weak i) n x).lineDeriv
  have hv : Tendsto (fun n => value (un n)) atTop (𝓝 (hf.toLp f)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fn
      (fun n => (hfn n).continuous.memLp_of_hasCompactSupport (hsn n)) f hf).mpr
    exact mollification_tendsto_global hf hs
  have hd (i : Fin d) : Tendsto (fun n => derivative i (un n))
      atTop (𝓝 ((hdf i).toLp (df i))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n x => fderiv ℝ (fn n) x (EuclideanSpace.single i 1))
      (fun n => ((hfn n).continuous_fderiv (by simp)).clm_apply continuous_const
        |>.memLp_of_hasCompactSupport ((hsn n).fderiv_apply ℝ _))
      (df i) (hdf i)).mpr
    simp_rw [hdn]
    exact mollification_tendsto_global (hdf i) (hds i)
  have hlim : Tendsto un atTop (𝓝 (ofFunctions f df hf hdf hw)) :=
    tendsto_subtype_rng.mpr (hv.prodMk_nhds (tendsto_pi_nhds.mpr hd))
  apply isClosed_closure.mem_of_tendsto hlim
  exact Eventually.of_forall fun n => subset_closure ⟨fn n, hfn n, hsn n, rfl⟩

/-- The smooth compact core is dense without any supplied approximation premise. -/
theorem dense_smoothCore : Dense (smoothCore E d) := by
  intro u
  apply isClosed_closure.mem_of_tendsto (cutoffH1_tendsto u)
  exact Eventually.of_forall fun n =>
    mem_closure_smoothCore_of_compact (cutoffValue u n) (cutoffGradient u n)
      (cutoffValue_memLp u n) (cutoffGradient_memLp u n) (cutoff_weak u n)
      (cutoffValue_hasCompactSupport u n) (cutoffGradient_hasCompactSupport u n)

end GptLean.ElectronicH1Core
