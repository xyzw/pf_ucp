import PfHk.RadialGaugeConnection
import PfHk.RadialGaugeEnergyLabel
import GptLean.WeylFormDisplacement
import GptLean.WeylPhaseFinite

/-!
The radial gauge acts on the actual radiation form domain. On the common
finite-photon core, differentiating its Weyl action gives the exact
covariant derivative with connection `A - ∇h`. No gauge-transformation
formula for the physical fields is an assumption.
-/

noncomputable section
namespace PfHk.RadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability GptLean.PhysicalWeyl Gaussian PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace Interval

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
attribute [local irreducible] radiationGraphDerivative radiationGraphInclusion
  weylWeightedGraph kernelField unitary

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)

theorem contraction_fixed (X v : Configuration N) :
    F.conjugation (contraction F χ e X v).val.1 = (contraction F χ e X v).val.1 :=
  sum_fixed F _ (fun j => real_smul_fixed F _ _ (couplingKernel_fixed F χ e j X))

theorem labelIntegrandDerivative_fixed (X v : Configuration N) (t s : ℝ) :
    F.conjugation (labelIntegrandDerivative F χ hUV e X v t s).val.1 =
      (labelIntegrandDerivative F χ hUV e X v t s).val.1 := by
  apply add_fixed F
  · exact sum_fixed F _ (fun j => real_smul_fixed F _ _ (couplingKernel_fixed F χ e j _))
  · exact sum_fixed F _ (fun j => real_smul_fixed F _ _ (couplingDerivative_fixed F χ hUV e j v _))

theorem labelDerivative_fixed (X v : Configuration N) :
    F.conjugation (labelDerivative F χ hUV e X v).val.1 =
      (labelDerivative F χ hUV e X v).val.1 := by
  apply integral_fixed F
  · exact ((labelIntegrandDerivative_continuous F χ hUV e X v).comp
      ((continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).prodMk continuous_id)).intervalIntegrable 0 1
  · exact labelIntegrandDerivative_fixed F χ hUV e X v 0

theorem radialConnection_fixed (X v : Configuration N) :
    F.conjugation (radialConnection F χ hUV e X v).val.1 =
      (radialConnection F χ hUV e X v).val.1 := by
  rw [radialConnection_eq]
  change F.realStructure.realCLM (_ - _) = _ - _
  rw [map_sub]
  exact congrArg₂ (fun a b : Lp ℂ 2 photonMeasure => a - b)
    (contraction_fixed F χ e X v) (labelDerivative_fixed F χ hUV e X v)

theorem imaginary_label_relation (X : Configuration N) :
    ∀ᵐ p ∂photonMeasure, (Complex.I • sqrtLabel F χ hUV e X) p =
      (Real.sqrt ‖p.1‖ : ℂ) * (Complex.I • (label F χ e X).val.1) p := by
  filter_upwards [sqrtLabel_relation F χ hUV e X,
    Lp.coeFn_smul Complex.I (sqrtLabel F χ hUV e X),
    Lp.coeFn_smul Complex.I (label F χ e X).val.1] with p hp hq hr
  simp only [Pi.smul_apply, smul_eq_mul] at hq hr
  rw [hq, hr, hp]
  ring

/-- The radial Weyl unitary lifted to the full radiation graph domain. -/
def graphLift (W : ConcreteWeylLaw photonMeasure) (X : Configuration N) :
    RadiationGraphSpace →L[ℂ] RadiationGraphSpace :=
  weylWeightedGraph W (Complex.I • (label F χ e X).val.1)
    (Complex.I • sqrtLabel F χ hUV e X) (imaginary_label_relation F χ hUV e X)

theorem graphLift_inclusion (W : ConcreteWeylLaw photonMeasure)
    (X : Configuration N) (q : RadiationGraphSpace) :
    radiationGraphInclusion (graphLift F χ hUV e W X q) =
      unitary F χ e W X (radiationGraphInclusion q) := by
  simpa only [graphLift, unitary] using
    weylWeightedGraph_inclusion W (Complex.I • (label F χ e X).val.1)
      (Complex.I • sqrtLabel F χ hUV e X) (imaginary_label_relation F χ hUV e X) q

/-- Every label in the physical real family, including the curvature,
commutes with the radial Weyl unitary on the full radiation form domain. -/
theorem real_field_covariance (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (X : Configuration N) (k : WeightedPhotonKernel)
    (hk : F.conjugation k.val.1 = k.val.1) (q : RadiationGraphSpace) :
    kernelField C k (graphLift F χ hUV e W X q) =
      unitary F χ e W X (kernelField C k q) := by
  have hi : (⟪k.val.1, (label F χ e X).val.1⟫_ℂ).im = 0 :=
    realStructure_fixed_inner_im photonMeasure F.realStructure
      ⟨_, (F.realStructure.mem_fixedSpace _).mpr hk⟩
      ⟨_, (F.realStructure.mem_fixedSpace _).mpr (label_fixed F χ e X)⟩
  simpa only [graphLift, unitary, inner_smul_right, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, hi, zero_sub, neg_zero, mul_zero, Complex.ofReal_zero,
    zero_smul, add_zero] using
    kernelField_weylWeightedGraph W (Complex.I • (label F χ e X).val.1)
      (Complex.I • sqrtLabel F χ hUV e X) (imaginary_label_relation F χ hUV e X) C k q

/-- The finite-sector generator is the same field as the radiation-domain
operator wherever both representations apply. -/
theorem finiteField_eq (C : CanonicalSectorCCR photonMeasure) (k : WeightedPhotonKernel)
    (q : RadiationGraphSpace) (M : ℕ)
    (hM : FiniteNumberSupport photonMeasure M (radiationGraphInclusion q)) :
    creationFinite photonMeasure M k.val.1 (radiationGraphInclusion q) +
      annihilationFinite photonMeasure M k.val.1 (radiationGraphInclusion q) = kernelField C k q := by
  apply lp.ext
  funext n
  exact (WeylPhase.finite_segalGraph photonMeasure M k.val.1 _ hM n).trans
    (kernelField_segalGraph C k q n).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Differentiation of the actual spatially dependent Weyl action on a
finite-photon core vector. The moving vector only needs a strong derivative. -/
theorem unitary_hasDerivAt_apply (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (X v : Configuration N)
    (z : ℝ → PhotonFock) (dz : PhotonFock) (hz : HasDerivAt z dz 0)
    (q : RadiationGraphSpace) (hz0 : z 0 = radiationGraphInclusion q) (M : ℕ)
    (hM : FiniteNumberSupport photonMeasure M (radiationGraphInclusion q)) :
    HasDerivAt (fun t => unitary F χ e W (X + t • v) (z t))
      (unitary F χ e W X (Complex.I • kernelField C (labelDerivative F χ hUV e X v) q + dz)) 0 := by
  have hd : HasDerivAt (fun t : ℝ => Complex.I • (label F χ e (X + t • v)).val.1)
      (Complex.I • (labelDerivative F χ hUV e X v).val.1) 0 := by
    convert! (((component false).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (label_hasLineDerivAt F χ hUV e X v)).const_smul Complex.I) using 1
  have hh := W.hasDerivAt_apply photonMeasure hd hz M (by rw [hz0]; exact hM)
  simp only [zero_smul, add_zero, hz0, finiteWeylDerivative_apply,
    WeylPhase.creationFinite_kernel_smul, WeylPhase.annihilationFinite_kernel_smul,
    Complex.conj_I] at hh
  have hi : (⟪Complex.I • (label F χ e X).val.1,
      Complex.I • (labelDerivative F χ hUV e X v).val.1⟫_ℂ).im = 0 := by
    have hreal := realStructure_fixed_inner_im photonMeasure F.realStructure
      ⟨_, (F.realStructure.mem_fixedSpace _).mpr (label_fixed F χ e X)⟩
      ⟨_, (F.realStructure.mem_fixedSpace _).mpr (labelDerivative_fixed F χ hUV e X v)⟩
    have he : ⟪Complex.I • (label F χ e X).val.1,
        Complex.I • (labelDerivative F χ hUV e X v).val.1⟫_ℂ =
        ⟪(label F χ e X).val.1, (labelDerivative F χ hUV e X v).val.1⟫_ℂ := by
      simp only [inner_smul_left, inner_smul_right, Complex.conj_I, mul_neg,
        ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    rw [he]
    exact hreal
  simp only [hi, Complex.ofReal_zero, mul_zero, zero_smul, add_zero,
    neg_smul, sub_neg_eq_add, ← smul_add, finiteField_eq C _ q M hM, ← map_add] at hh
  simpa only [unitary] using hh

/-- The pointwise covariant derivative identity on the common finite-photon
core, with the connection identified by the proved curvature formula. -/
theorem covariant_derivative_identity (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (X v : Configuration N)
    (q : RadiationGraphSpace) (du : PhotonFock) :
    unitary F χ e W X ((-Complex.I) • du + kernelField C (contraction F χ e X v) q) =
      (-Complex.I) • unitary F χ e W X
        (Complex.I • kernelField C (labelDerivative F χ hUV e X v) q + du) +
      kernelField C (radialConnection F χ hUV e X v) (graphLift F χ hUV e W X q) := by
  rw [real_field_covariance F χ hUV e C W X _ (radialConnection_fixed F χ hUV e X v),
    radialConnection_eq]
  change _ = (-Complex.I) • unitary F χ e W X _ +
    unitary F χ e W X ((kernelFieldMap C) (_ - _) q)
  rw [map_sub]
  change _ = (-Complex.I) • unitary F χ e W X _ +
    unitary F χ e W X (kernelField C (contraction F χ e X v) q -
      kernelField C (labelDerivative F χ hUV e X v) q)
  simp only [map_add, map_sub, map_smul, smul_add, smul_smul, neg_mul,
    Complex.I_mul_I, neg_neg, one_smul]
  abel

end PfHk.RadialGauge
