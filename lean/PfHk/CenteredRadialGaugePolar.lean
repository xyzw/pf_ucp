import PfHk.CenteredRadialGaugeCovariance
import PfHk.CenteredRadialGaugeConnection
import PfHk.CenteredRadialGaugeRadiation
import PfHk.PolarCalculus

/-!
First-order polar substitution for the actual PF fields and Weyl gauge
about an arbitrary electronic center O.
The ordinary polar identities are the universal `StandardPolarCalculus`
background. Every physical coefficient and its gauge transformation is
proved from the concrete kernels. The regularity hypotheses below describe
the pointwise core on which ordinary derivatives can be evaluated. They do
not assert a physical operator identity or a Carleman estimate.
-/

noncomputable section
namespace PfHk.CenteredRadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

local instance photonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.complexToReal

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ) (O : Configuration N)

/-- A radiation graph valued wave, with its actual Fock representative. -/
def coreValue (q : Configuration N → RadiationGraphSpace) (X : Configuration N) : PhotonFock :=
  radiationGraphInclusion (q X)

def gaugedValue (W : ConcreteWeylLaw photonMeasure)
    (q : Configuration N → RadiationGraphSpace) (X : Configuration N) : PhotonFock :=
  unitary F χ e O W X (coreValue q X)

/-- Strong directional Weyl differentiation identifies the ordinary
Fréchet derivative wherever the gauged core representative is differentiable. -/
theorem gaugedValue_fderiv (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (q : Configuration N → RadiationGraphSpace)
    (X v : Configuration N) (hu : DifferentiableAt ℝ (coreValue q) X)
    (hw : DifferentiableAt ℝ (gaugedValue F χ e O W q) X) (M : ℕ)
    (hM : FiniteNumberSupport photonMeasure M (coreValue q X)) :
    fderiv ℝ (gaugedValue F χ e O W q) X v =
      unitary F χ e O W X (Complex.I • kernelField C (labelDerivative F χ hUV e O X v) (q X) +
        fderiv ℝ (coreValue q) X v) := by
  have hd := unitary_hasDerivAt_apply F χ hUV e O C W X v
    (fun t => coreValue q (X + t • v)) (fderiv ℝ (coreValue q) X v)
    (hu.hasFDerivAt.hasLineDerivAt v) (q X) (by simp only [zero_smul, add_zero, coreValue]) M hM
  exact (hw.hasFDerivAt.hasLineDerivAt v).unique hd

theorem contraction_single (X : Configuration N) (j : Fin N × Fin 3) :
    contraction F χ e O X (EuclideanSpace.single j 1) = couplingKernel F χ e O j X := by
  simp [contraction]

/-- The original physical covariant derivative, with `g_j=-e G_j`. -/
def coreCovariant (C : CanonicalSectorCCR photonMeasure)
    (q : Configuration N → RadiationGraphSpace) (j : Fin N × Fin 3) (X : Configuration N) : PhotonFock :=
  (-Complex.I) • fderiv ℝ (coreValue q) X (EuclideanSpace.single j 1) +
    kernelField C (couplingKernel F χ e O j X) (q X)

/-- The radial-gauge connection acting on the actual gauged graph vector. -/
def connectionAction (C : CanonicalSectorCCR photonMeasure) (W : ConcreteWeylLaw photonMeasure)
    (q : Configuration N → RadiationGraphSpace) (j : Fin N × Fin 3) (X : Configuration N) : PhotonFock :=
  kernelField C (radialConnection F χ hUV e O X (EuclideanSpace.single j 1))
    (graphLift F χ hUV e O W X (q X))

/-- Gauge covariance of the actual pointwise kinetic norm. -/
theorem coreCovariant_norm (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (q : Configuration N → RadiationGraphSpace)
    (X : Configuration N) (j : Fin N × Fin 3)
    (hu : DifferentiableAt ℝ (coreValue q) X)
    (hw : DifferentiableAt ℝ (gaugedValue F χ e O W q) X) (M : ℕ)
    (hM : FiniteNumberSupport photonMeasure M (coreValue q X)) :
    ‖coreCovariant F χ e O C q j X‖ =
      ‖PolarCalculus.covariant (gaugedValue F χ e O W q)
        (connectionAction F χ hUV e O C W q) j X‖ := by
  have h := covariant_derivative_identity F χ hUV e O C W X (EuclideanSpace.single j 1)
    (q X) (fderiv ℝ (coreValue q) X (EuclideanSpace.single j 1))
  rw [contraction_single, ← gaugedValue_fderiv F χ hUV e O C W q X
    (EuclideanSpace.single j 1) hu hw M hM] at h
  have hn := congrArg norm h
  exact ((unitary F χ e O W X).norm_map (coreCovariant F χ e O C q j X)).symm.trans hn

/-- The physical connection has no radial action, at every positive radius. -/
theorem connectionAction_tangent (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (q : Configuration N → RadiationGraphSpace)
    (θ : Configuration N) {r : ℝ} (hr : 0 < r) :
    (∑ j : Fin N × Fin 3, θ j • connectionAction F χ hUV e O C W q j (r • θ)) = 0 := by
  have h := radialConnection_components F χ hUV e O (r • θ)
  have hs : r • (∑ j : Fin N × Fin 3,
      θ j • radialConnection F χ hUV e O (r • θ) (EuclideanSpace.single j 1)) = 0 := by
    rw [Finset.smul_sum]
    simpa only [smul_smul, PiLp.smul_apply, smul_eq_mul] using h
  have hz := (smul_eq_zero.mp hs).resolve_left hr.ne'
  change (∑ j : Fin N × Fin 3, θ j •
    RadialGauge.fieldEvaluation C (graphLift F χ hUV e O W (r • θ) (q (r • θ)))
      (radialConnection F χ hUV e O (r • θ) (EuclideanSpace.single j 1))) = 0
  simp_rw [← map_smul]
  rw [← map_sum, hz, map_zero]

/-- The angular field action is the proved curvature integral. -/
theorem angularAction_eq (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (q : Configuration N → RadiationGraphSpace)
    (θ : Configuration N) (r : ℝ) (j : Fin N × Fin 3) :
    kernelField C (angularLabel F χ hUV e O θ (EuclideanSpace.single j 1) r)
        (graphLift F χ hUV e O W (r • θ) (q (r • θ))) =
      r • connectionAction F χ hUV e O C W q j (r • θ) := by
  have h := congrArg
    (RadialGauge.fieldEvaluation C (graphLift F χ hUV e O W (r • θ) (q (r • θ))))
    (angularLabel_eq_radialConnection F χ hUV e O θ (EuclideanSpace.single j 1) r)
  rw [map_smul] at h
  exact h

private theorem angular_phase_norm (p f : PhotonFock) :
    ‖(-Complex.I) • p + f‖ = ‖p + Complex.I • f‖ := by
  calc
    _ = ‖Complex.I • ((-Complex.I) • p + f)‖ := by
      simp only [norm_smul, Complex.norm_I, one_mul]
    _ = _ := by
      simp only [smul_add, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]

/-- The actual angular derivative in the convention of the sphere form. -/
def angularCore (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (q : Configuration N → RadiationGraphSpace)
    (r : ℝ) (θ : PolarCalculus.UnitSphere (Fin N × Fin 3)) (j : Fin N × Fin 3) : PhotonFock :=
  PolarCalculus.sphereGradient
    (PolarCalculus.radialRestriction (gaugedValue F χ e O W q) r) j θ +
      Complex.I • kernelField C (angularLabel F χ hUV e O θ.val (EuclideanSpace.single j 1) r)
        (graphLift F χ hUV e O W (r • θ.val) (q (r • θ.val)))

attribute [local irreducible] coreValue gaugedValue coreCovariant connectionAction
  kernelField graphLift angularLabel radialConnection

set_option backward.isDefEq.respectTransparency.types true in
/-- Full physical kinetic splitting in the sphere coordinates used by the
angular form estimates. No derivative of the physical curvature is needed. -/
theorem physical_polar_kinetic (P : PolarCalculus.StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (C : CanonicalSectorCCR photonMeasure) (W : ConcreteWeylLaw photonMeasure)
    (q : Configuration N → RadiationGraphSpace)
    (hw : ContDiff ℝ (1 : ℕ∞) (gaugedValue F χ e O W q))
    {r : ℝ} (hr : 0 < r) (θ : PolarCalculus.UnitSphere (Fin N × Fin 3))
    (hs : PolarCalculus.SphereC1 (PolarCalculus.radialRestriction (gaugedValue F χ e O W q) r))
    (hu : DifferentiableAt ℝ (coreValue q) (r • (θ : Configuration N))) (M : ℕ)
    (hM : FiniteNumberSupport photonMeasure M (coreValue q (r • (θ : Configuration N)))) :
    r ^ 2 * (∑ j : Fin N × Fin 3, ‖coreCovariant F χ e O C q j (r • (θ : Configuration N))‖ ^ 2) =
      r ^ 2 * ‖PolarCalculus.radialFirst (gaugedValue F χ e O W q) r θ‖ ^ 2 +
        ∑ j : Fin N × Fin 3, ‖angularCore F χ hUV e O C W q r θ j‖ ^ 2 := by
  have hnorm (j : Fin N × Fin 3) := coreCovariant_norm F χ hUV e O C W q
    (r • θ.val) j hu ((hw.differentiable one_ne_zero).differentiableAt) M hM
  simp_rw [hnorm]
  rw [PolarCalculus.covariant_norm_decomposition P _ hw _ hr θ hs
    (connectionAction_tangent F χ hUV e O C W q θ.val hr)]
  apply congrArg (fun s : ℝ =>
    r ^ 2 * ‖PolarCalculus.radialFirst (gaugedValue F χ e O W q) r θ‖ ^ 2 + s)
  apply Finset.sum_congr rfl
  intro j _
  unfold PolarCalculus.angularCovariant angularCore
  let p := PolarCalculus.sphereGradient
    (PolarCalculus.radialRestriction (gaugedValue F χ e O W q) r) j θ
  let f := kernelField C (angularLabel F χ hUV e O θ.val (EuclideanSpace.single j 1) r)
    (graphLift F χ hUV e O W (r • θ.val) (q (r • θ.val)))
  have hA := angularAction_eq F χ hUV e O C W q θ.val r j
  have h₁ := congrArg (fun z : PhotonFock => ‖(-Complex.I) • p + z‖ ^ 2) hA.symm
  have h₂ := congrArg (fun z : ℝ => z ^ 2) (angular_phase_norm p f)
  convert! h₁.trans h₂ using 1

/-- The two actual Weyl graph maps are inverse. This uses uniqueness in the
closed radiation graph, not an additional gauge-domain hypothesis. -/
theorem inverse_graphLift (W : ConcreteWeylLaw photonMeasure)
    (X : Configuration N) (q : RadiationGraphSpace) :
    inverseRadiationGraph F χ hUV e O W X (graphLift F χ hUV e O W X q) = q := by
  have hi : radiationGraphInclusion
      (inverseRadiationGraph F χ hUV e O W X (graphLift F χ hUV e O W X q)) = radiationGraphInclusion q := by
    rw [inverseRadiationGraph_inclusion, graphLift_inclusion, LinearIsometryEquiv.symm_apply_apply]
  have hz : (inverseRadiationGraph F χ hUV e O W X (graphLift F χ hUV e O W X q) - q).val.1 = 0 :=
    sub_eq_zero.mpr hi
  have ho := radiationRoot.graph_fst_eq_zero_snd
    (inverseRadiationGraph F χ hUV e O W X (graphLift F χ hUV e O W X q) - q).property hz
  apply Subtype.ext
  exact Prod.ext hi (sub_eq_zero.mp ho)

/-- The radiation term in the cylinder is exactly twice the original
physical radiation energy on the gauged vector. -/
theorem radiationForm_graphLift (W : ConcreteWeylLaw photonMeasure)
    (X : Configuration N) (q : RadiationGraphSpace) :
    radiationForm F χ hUV e O X (graphLift F χ hUV e O W X q) =
      2 * ‖radiationGraphDerivative q‖ ^ 2 := by
  rw [radiationForm_eq F χ hUV e O W, inverse_graphLift]

end PfHk.CenteredRadialGauge
