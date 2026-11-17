import PfHk.L2OperatorDerivative
import PfHk.RadialGaugeCurvature
import GptLean.PhysicalFockSpatialField

/-! Strong differentiation of the actual spatial Segal field on a fixed
radiation-domain vector. The proof lifts the pointwise label derivative
through dominated convergence in L2. -/

noncomputable section
namespace PfHk.SpatialFieldParameterDerivative

open MeasureTheory Filter GptLean GptLean.PhysicalFock
open scoped ENNReal Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000
attribute [local irreducible] kernelField radiationGraphInclusion radiationGraphDerivative

variable (C : CanonicalSectorCCR photonMeasure)

theorem field_norm_le_graph (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    ‖kernelField C k q‖ ≤ 3 * ‖k‖ * ‖q‖ := by
  have hf : ‖k.val.1‖ ≤ ‖k‖ := norm_fst_le k.val
  have hs : ‖k.val.2‖ ≤ ‖k‖ := norm_snd_le k.val
  have hqf : ‖radiationGraphInclusion q‖ ≤ ‖q‖ := by
    unfold radiationGraphInclusion
    exact norm_fst_le q.val
  have hqs : ‖radiationGraphDerivative q‖ ≤ ‖q‖ := by
    unfold radiationGraphDerivative
    exact norm_snd_le q.val
  have h₁ := mul_le_mul hs hqs (norm_nonneg _) (norm_nonneg k)
  have h₂ := mul_le_mul hf hqf (norm_nonneg _) (norm_nonneg k)
  nlinarith only [kernelField_norm_le C k q, h₁, h₂]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)


/-- A named L2 value avoids comparing scalar instances through the
continuous-linear-map coercion in a derivative statement. -/
def fieldValue (a : X → WeightedPhotonKernel) (ha : AEStronglyMeasurable a μ)
    (M : ℝ) (hM : ∀ᵐ x ∂μ, ‖a x‖ ≤ M) (q : SpatialRadiationGraph μ) :
    SpatialPhotonSpace μ := spatialField μ C a ha M hM q

attribute [local irreducible] fieldValue

set_option maxHeartbeats 80000 in

theorem spatialField_hasDerivAt (a : ℝ → X → WeightedPhotonKernel)
    (ha : ∀ s, AEStronglyMeasurable (a s) μ)
    (M : ℝ → ℝ) (hM : ∀ s, ∀ᵐ x ∂μ, ‖a s x‖ ≤ M s)
    (da : X → WeightedPhotonKernel) (hda : AEStronglyMeasurable da μ)
    (D : ℝ) (_hD : 0 ≤ D) (hdaBound : ∀ᵐ x ∂μ, ‖da x‖ ≤ D)
    (t : ℝ) (q : SpatialRadiationGraph μ)
    (hderivative : ∀ᵐ x ∂μ, HasDerivAt (fun s => a s x) (da x) t)
    (hslope : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖h⁻¹ • (a (t + h) x - a t x)‖ ≤ D) :
    L2OperatorDerivative.HasL2DerivAt (E := PhotonFock)
      (fun s => fieldValue C μ (a s) (ha s) (M s) (hM s) q)
      (fieldValue C μ da hda D hdaBound q) t := by
  let f : ℝ → X → PhotonFock := fun s x => kernelField C (a s x) (q x)
  let g : X → PhotonFock := fun x => kernelField C (da x) (q x)
  have hf (s : ℝ) : MemLp (f s) 2 μ :=
    (Lp.memLp (spatialField μ C (a s) (ha s) (M s) (hM s) q)).ae_eq
      (spatialField_ae μ C (a s) (ha s) (M s) (hM s) q)
  have hg : MemLp g 2 μ :=
    (Lp.memLp (spatialField μ C da hda D hdaBound q)).ae_eq
      (spatialField_ae μ C da hda D hdaBound q)
  have hdLp := L2OperatorDerivative.hasDerivAt_toLp
    (μ := μ) (K := WeightedPhotonKernel) (E := PhotonFock) (Q := RadiationGraphSpace)
    (fun x => RadialGauge.fieldEvaluation C (q x)) q (by norm_num : (0 : ℝ) ≤ 3)
    (fun x k => field_norm_le_graph C k (q x)) hf hg hdaBound hderivative hslope
  have hfun : (fun s => fieldValue C μ (a s) (ha s) (M s) (hM s) q) =
      (fun s => (hf s).toLp (f s)) := by
    funext s
    unfold fieldValue
    apply Lp.ext
    exact (spatialField_ae μ C (a s) (ha s) (M s) (hM s) q).trans (hf s).coeFn_toLp.symm
  have hval : fieldValue C μ da hda D hdaBound q = hg.toLp g := by
    unfold fieldValue
    apply Lp.ext
    exact (spatialField_ae μ C da hda D hdaBound q).trans hg.coeFn_toLp.symm
  rw [hfun, hval]
  convert! hdLp using 1

end PfHk.SpatialFieldParameterDerivative
