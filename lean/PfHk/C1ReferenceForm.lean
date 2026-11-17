import PfHk.C1ReferenceCore
import PfHk.PhysicalLocalEnergy
import PfHk.PolarInnerCalculus

/-! Evaluation of the actual free PF form on concrete C1 radiation-graph
representatives. This links the weak form graph to pointwise gauge and
polar calculations without postulating a physical evaluation formula. -/

noncomputable section
namespace PfHk.C1ReferenceCore

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPFFormEvaluation GptLean.Gaussian
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
local instance c1ReferenceFormPhotonRealInner : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] kernelField radiationGraphInclusion radiationGraphDerivative
  PhysicalPFReference.covariant PhysicalPFReference.field PhysicalPFReference.ordinary
  PhysicalPFReference.inclusion PhysicalPFReference.radiation PhysicalPFReference.potential reference

variable {I : Type} [Fintype I] [DecidableEq I]
  (C : CanonicalSectorCCR photonMeasure) (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume) (M : ℝ)
  (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

def covariantFunction (q : Position I → RadiationGraphSpace) (j : I) (x : Position I) : PhotonFock :=
  (-Complex.I) • derivativeFunction q j x - (e : ℂ) • kernelField C (κ j x) (q x)

theorem reference_field (q : Position I → RadiationGraphSpace) (hq : MemLp q 2 volume)
    (hf : ContDiff ℝ (1 : ℕ∞) (valueFunction q)) (hs : HasCompactSupport (valueFunction q)) (j : I) :
    field I (fun _ => 0) C κ hκ M hbound j (reference q hq hf hs) =ᵐ[volume]
      fun x => kernelField C (κ j x) (q x) := by
  apply reference_field_ae_of_graph I (fun _ => 0) C κ hκ M hbound
    (reference q hq hf hs) (valueFunction q) (fun x => kernelField C (κ j x) (q x)) j
  · rw [reference_value]
    exact (value_memLp q hq).coeFn_toLp
  · exact ae_of_all _ fun x => (segalOperator_graph_iff photonMeasure _ _ _).mpr
      (kernelField_segalGraph C (κ j x) (q x))

theorem reference_covariant (q : Position I → RadiationGraphSpace) (hq : MemLp q 2 volume)
    (hf : ContDiff ℝ (1 : ℕ∞) (valueFunction q)) (hs : HasCompactSupport (valueFunction q)) (j : I) :
    covariant I (fun _ => 0) C κ hκ M hbound e j (reference q hq hf hs) =ᵐ[volume]
      covariantFunction C κ e q j := by
  apply reference_covariant_ae I (fun _ => 0) C κ hκ M hbound e
    (reference q hq hf hs) (derivativeFunction q) (fun i x => kernelField C (κ i x) (q x))
  · intro i
    rw [reference_ordinary]
    exact (derivative_memLp q hf hs i).coeFn_toLp
  · exact reference_field C κ hκ M hbound q hq hf hs

def formDensity (q p : Position I → RadiationGraphSpace) (x : Position I) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, inner ℝ (covariantFunction C κ e q j x) (covariantFunction C κ e p j x) +
    inner ℝ (radiationGraphDerivative (q x)) (radiationGraphDerivative (p x))

theorem reference_radiation_ae (q : Position I → RadiationGraphSpace) (hq : MemLp q 2 volume)
    (hf : ContDiff ℝ (1 : ℕ∞) (valueFunction q)) (hs : HasCompactSupport (valueFunction q)) :
    radiation I (fun _ => 0) (reference q hq hf hs) =ᵐ[volume]
      fun x => radiationGraphDerivative (q x) := by
  rw [reference_radiation]
  convert! (radiationGraphDerivative.comp_memLp' hq).coeFn_toLp using 1

include hκ M hbound in
theorem formDensity_integrable (q p : Position I → RadiationGraphSpace)
    (hq : MemLp q 2 volume) (hp : MemLp p 2 volume)
    (hfq : ContDiff ℝ (1 : ℕ∞) (valueFunction q)) (hfp : ContDiff ℝ (1 : ℕ∞) (valueFunction p))
    (hsq : HasCompactSupport (valueFunction q)) (hsp : HasCompactSupport (valueFunction p)) :
    Integrable (formDensity C κ e q p) := by
  have hd (j : I) := PolarCalculus.l2_inner_integrable
    (covariant I (fun _ => 0) C κ hκ M hbound e j (reference q hq hfq hsq))
    (covariant I (fun _ => 0) C κ hκ M hbound e j (reference p hp hfp hsp))
    (reference_covariant C κ hκ M hbound e q hq hfq hsq j)
    (reference_covariant C κ hκ M hbound e p hp hfp hsp j)
  have hr := PolarCalculus.l2_inner_integrable
    (radiation I (fun _ => 0) (reference q hq hfq hsq))
    (radiation I (fun _ => 0) (reference p hp hfp hsp))
    (reference_radiation_ae q hq hfq hsq) (reference_radiation_ae p hp hfp hsp)
  exact ((integrable_finsetSum _ fun j _ => hd j).const_mul (1 / 2 : ℝ)).add hr

/-- Evaluation of the existing physical free form, with no extra form
or operator realization assumption. -/
theorem form_eq_integral (q p : Position I → RadiationGraphSpace)
    (hq : MemLp q 2 volume) (hp : MemLp p 2 volume)
    (hfq : ContDiff ℝ (1 : ℕ∞) (valueFunction q)) (hfp : ContDiff ℝ (1 : ℕ∞) (valueFunction p))
    (hsq : HasCompactSupport (valueFunction q)) (hsp : HasCompactSupport (valueFunction p)) :
    (PhysicalLocalEnergy.form (fun _ => 0) C κ hκ M hbound e
      (reference q hq hfq hsq) (reference p hp hfp hsp)).re =
        ∫ x, formDensity C κ e q p x := by
  let a : ℂ := (1 / 2 : ℂ) * ∑ j,
    inner ℂ (covariant I (fun _ => 0) C κ hκ M hbound e j (reference q hq hfq hsq))
      (covariant I (fun _ => 0) C κ hκ M hbound e j (reference p hp hfp hsp)) +
    inner ℂ (radiation I (fun _ => 0) (reference q hq hfq hsq))
      (radiation I (fun _ => 0) (reference p hp hfp hsp))
  have hzq := reference_potential q hq hfq hsq
  have hz := (congrArg (fun w : WaveSpace I =>
    inner ℂ w (potential I (fun _ => 0) (reference p hp hfp hsp))) hzq).trans
      (inner_zero_left _)
  have hform : PhysicalLocalEnergy.form (fun _ => 0) C κ hκ M hbound e
      (reference q hq hfq hsq) (reference p hp hfp hsp) = a :=
    (congrArg (fun b : ℂ => a + b) hz).trans (add_zero a)
  apply (congrArg Complex.re hform).trans
  exact PolarCalculus.l2_freeForm_eq_integral
    (fun j => covariant I (fun _ => 0) C κ hκ M hbound e j (reference q hq hfq hsq))
    (fun j => covariant I (fun _ => 0) C κ hκ M hbound e j (reference p hp hfp hsp))
    (radiation I (fun _ => 0) (reference q hq hfq hsq))
    (radiation I (fun _ => 0) (reference p hp hfp hsp))
    (reference_covariant C κ hκ M hbound e q hq hfq hsq)
    (reference_covariant C κ hκ M hbound e p hp hfp hsp)
    (reference_radiation_ae q hq hfq hsq) (reference_radiation_ae p hp hfp hsp)

end PfHk.C1ReferenceCore
