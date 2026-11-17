import PfHk.CenteredRadialGaugePolar
import PfHk.PolarInnerCalculus

/-! Bilinear first-order polar substitution for the genuine centered
Pauli–Fierz field. This is the pointwise identity used in weak form
transport. It differentiates the Weyl gauge only once. -/

noncomputable section
namespace PfHk.CenteredRadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability GptLean.PhysicalWeyl Gaussian PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
local instance centeredPolarInnerPhotonRealInner : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
local instance centeredPolarInnerAnalysisRealInner : InnerProductSpace ℝ (lp (fun _ : ℕ => PhotonFock) 2) :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] coreValue gaugedValue coreCovariant connectionAction
  kernelField graphLift angularLabel radialConnection angularCore
  radiationGraphDerivative radiationAnalysis coefficientTensor RadialGaugeRadiation.displacedAnalysis

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N)

theorem coreCovariant_gauge (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (q : Configuration N → RadiationGraphSpace)
    (X : Configuration N) (j : Fin N × Fin 3)
    (hu : DifferentiableAt ℝ (coreValue q) X)
    (hw : DifferentiableAt ℝ (gaugedValue F χ e O W q) X) (M : ℕ)
    (hM : FiniteNumberSupport photonMeasure M (coreValue q X)) :
    unitary F χ e O W X (coreCovariant F χ e O C q j X) =
      PolarCalculus.covariant (gaugedValue F χ e O W q)
        (connectionAction F χ hUV e O C W q) j X := by
  have h := covariant_derivative_identity F χ hUV e O C W X (EuclideanSpace.single j 1)
    (q X) (fderiv ℝ (coreValue q) X (EuclideanSpace.single j 1))
  rw [contraction_single, ← gaugedValue_fderiv F χ hUV e O C W q X
    (EuclideanSpace.single j 1) hu hw M hM] at h
  unfold coreCovariant PolarCalculus.covariant connectionAction
  convert! h using 1

theorem coreCovariant_inner (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (q p : Configuration N → RadiationGraphSpace)
    (X : Configuration N) (j : Fin N × Fin 3)
    (huq : DifferentiableAt ℝ (coreValue q) X)
    (hup : DifferentiableAt ℝ (coreValue p) X)
    (hwq : DifferentiableAt ℝ (gaugedValue F χ e O W q) X)
    (hwp : DifferentiableAt ℝ (gaugedValue F χ e O W p) X) (M K : ℕ)
    (hq : FiniteNumberSupport photonMeasure M (coreValue q X))
    (hp : FiniteNumberSupport photonMeasure K (coreValue p X)) :
    inner ℝ (coreCovariant F χ e O C q j X) (coreCovariant F χ e O C p j X) =
      inner ℝ (PolarCalculus.covariant (gaugedValue F χ e O W q)
        (connectionAction F χ hUV e O C W q) j X)
      (PolarCalculus.covariant (gaugedValue F χ e O W p)
        (connectionAction F χ hUV e O C W p) j X) := by
  have h := (PolarCalculus.complexIsometry_real_inner (unitary F χ e O W X)
    (coreCovariant F χ e O C q j X) (coreCovariant F χ e O C p j X)).symm
  rw [coreCovariant_gauge F χ hUV e O C W q X j huq hwq M hq,
    coreCovariant_gauge F χ hUV e O C W p X j hup hwp K hp] at h
  exact h

private theorem angular_phase_inner (p f q g : PhotonFock) :
    inner ℝ ((-Complex.I) • p + f) ((-Complex.I) • q + g) =
      inner ℝ (p + Complex.I • f) (q + Complex.I • g) := by
  have h := (PolarCalculus.phaseIsometry Complex.I Complex.norm_I : PhotonFock →ₗᵢ[ℝ] PhotonFock).inner_map_map ((-Complex.I) • p + f) ((-Complex.I) • q + g)
  change inner ℝ (Complex.I • ((-Complex.I) • p + f))
    (Complex.I • ((-Complex.I) • q + g)) = _ at h
  simpa only [smul_add, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul] using h.symm

theorem angularCore_inner (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (q p : Configuration N → RadiationGraphSpace)
    (r : ℝ) (θ : PolarCalculus.UnitSphere (Fin N × Fin 3)) (j : Fin N × Fin 3) :
    inner ℝ (PolarCalculus.angularCovariant (gaugedValue F χ e O W q)
      (connectionAction F χ hUV e O C W q) r j θ)
      (PolarCalculus.angularCovariant (gaugedValue F χ e O W p)
      (connectionAction F χ hUV e O C W p) r j θ) =
        inner ℝ (angularCore F χ hUV e O C W q r θ j)
          (angularCore F χ hUV e O C W p r θ j) := by
  unfold PolarCalculus.angularCovariant angularCore
  have hq := angularAction_eq F χ hUV e O C W q θ.val r j
  have hp := angularAction_eq F χ hUV e O C W p θ.val r j
  let a := PolarCalculus.sphereGradient
    (PolarCalculus.radialRestriction (gaugedValue F χ e O W q) r) j θ
  let b := PolarCalculus.sphereGradient
    (PolarCalculus.radialRestriction (gaugedValue F χ e O W p) r) j θ
  let f := kernelField C (angularLabel F χ hUV e O θ.val (EuclideanSpace.single j 1) r)
    (graphLift F χ hUV e O W (r • θ.val) (q (r • θ.val)))
  let g := kernelField C (angularLabel F χ hUV e O θ.val (EuclideanSpace.single j 1) r)
    (graphLift F χ hUV e O W (r • θ.val) (p (r • θ.val)))
  have h₁ := congrArg₂ (fun x y : PhotonFock =>
    inner ℝ ((-Complex.I) • a + x) ((-Complex.I) • b + y)) hq.symm hp.symm
  have h₂ := angular_phase_inner a f b g
  convert! h₁.trans h₂ using 1

/-- The actual bilinear kinetic form in polar coordinates. -/
theorem physical_polar_kinetic_inner
    (P : PolarCalculus.StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (C : CanonicalSectorCCR photonMeasure) (W : ConcreteWeylLaw photonMeasure)
    (q p : Configuration N → RadiationGraphSpace)
    (hwq : ContDiff ℝ (1 : ℕ∞) (gaugedValue F χ e O W q))
    (hwp : ContDiff ℝ (1 : ℕ∞) (gaugedValue F χ e O W p))
    {r : ℝ} (hr : 0 < r) (θ : PolarCalculus.UnitSphere (Fin N × Fin 3))
    (hsq : PolarCalculus.SphereC1 (PolarCalculus.radialRestriction (gaugedValue F χ e O W q) r))
    (hsp : PolarCalculus.SphereC1 (PolarCalculus.radialRestriction (gaugedValue F χ e O W p) r))
    (huq : DifferentiableAt ℝ (coreValue q) (r • θ.val))
    (hup : DifferentiableAt ℝ (coreValue p) (r • θ.val)) (M K : ℕ)
    (hq : FiniteNumberSupport photonMeasure M (coreValue q (r • θ.val)))
    (hp : FiniteNumberSupport photonMeasure K (coreValue p (r • θ.val))) :
    r ^ 2 * (∑ j, inner ℝ (coreCovariant F χ e O C q j (r • θ.val))
      (coreCovariant F χ e O C p j (r • θ.val))) =
      r ^ 2 * inner ℝ (PolarCalculus.radialFirst (gaugedValue F χ e O W q) r θ)
        (PolarCalculus.radialFirst (gaugedValue F χ e O W p) r θ) +
      ∑ j, inner ℝ (angularCore F χ hUV e O C W q r θ j)
        (angularCore F χ hUV e O C W p r θ j) := by
  have hinner (j : Fin N × Fin 3) := coreCovariant_inner F χ hUV e O C W q p
    (r • θ.val) j huq hup ((hwq.differentiable one_ne_zero).differentiableAt)
      ((hwp.differentiable one_ne_zero).differentiableAt) M K hq hp
  simp_rw [hinner]
  rw [PolarCalculus.covariant_inner_decomposition P _ _ hwq hwp _ _ hr θ hsq hsp
    (connectionAction_tangent F χ hUV e O C W q θ.val hr)
    (connectionAction_tangent F χ hUV e O C W p θ.val hr)]
  apply congrArg (fun a : ℝ => r ^ 2 *
    inner ℝ (PolarCalculus.radialFirst (gaugedValue F χ e O W q) r θ)
      (PolarCalculus.radialFirst (gaugedValue F χ e O W p) r θ) + a)
  exact Finset.sum_congr rfl fun j _ => angularCore_inner F χ hUV e O C W q p r θ j

/-- Bilinear radiation transport follows by real polarization of the
already proved actual Weyl radiation energy identity. -/
theorem radiationPair_graphLift (W : ConcreteWeylLaw photonMeasure)
    (X : Configuration N) (q p : RadiationGraphSpace) :
    2 * inner ℝ
      (RadialGaugeRadiation.displacedAnalysis (inverseSqrtLabel F χ hUV e O X)
        (graphLift F χ hUV e O W X q))
      (RadialGaugeRadiation.displacedAnalysis (inverseSqrtLabel F χ hUV e O X)
        (graphLift F χ hUV e O W X p)) =
      2 * inner ℝ (radiationGraphDerivative q) (radiationGraphDerivative p) := by
  have hq := radiationForm_graphLift F χ hUV e O W X q
  have hp := radiationForm_graphLift F χ hUV e O W X p
  have hsum := radiationForm_graphLift F χ hUV e O W X (q + p)
  unfold radiationForm RadialGaugeRadiation.energy at hq hp hsum
  have ha : RadialGaugeRadiation.displacedAnalysis (inverseSqrtLabel F χ hUV e O X)
      (graphLift F χ hUV e O W X (q + p)) =
      RadialGaugeRadiation.displacedAnalysis (inverseSqrtLabel F χ hUV e O X)
        (graphLift F χ hUV e O W X q) +
      RadialGaugeRadiation.displacedAnalysis (inverseSqrtLabel F χ hUV e O X)
        (graphLift F χ hUV e O W X p) := by
    simp only [RadialGaugeRadiation.displacedAnalysis, map_add]
    abel
  have hs := (congrArg (fun v : lp (fun _ : ℕ => PhotonFock) 2 => 2 * ‖v‖ ^ 2) ha).symm.trans
    (hsum.trans (congrArg (fun v : PhotonFock => 2 * ‖v‖ ^ 2)
      (map_add radiationGraphDerivative q p)))
  have hn₁ := norm_add_sq_real
    (RadialGaugeRadiation.displacedAnalysis (inverseSqrtLabel F χ hUV e O X)
      (graphLift F χ hUV e O W X q))
    (RadialGaugeRadiation.displacedAnalysis (inverseSqrtLabel F χ hUV e O X)
      (graphLift F χ hUV e O W X p))
  have hn₂ := norm_add_sq_real (radiationGraphDerivative q) (radiationGraphDerivative p)
  linarith only [hq, hp, hs, hn₁, hn₂]

end PfHk.CenteredRadialGauge
