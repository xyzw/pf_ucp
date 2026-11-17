import PfHk.PauliMagneticWeakDerivative
import PfHk.RadialGaugeCurvature
import PfHk.WeylCoreReference
import GptLean.PhysicalFockFieldSymmetry
import PfHk.PhysicalFormProductRules


/-! The weak ordinary/quantum-field product rule on the actual smooth
radiation graph core. The physical coupling labels need only the stated
first ultraviolet moment. -/

noncomputable section
namespace PfHk.PauliMagneticWeakCore

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.PhysicalOperatorDomain PfHk.PhysicalFieldRegularity
open MeasureTheory.Measure
open scoped ContDiff InnerProductSpace Topology

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

section ComplexField

variable {E Q K H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedSpace ℂ Q]
  [IsScalarTower ℝ ℂ Q]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The exact weak product identity, with the actual graph
operators retained as arguments. -/
def ProductPairing (ν : Measure E) (J : Q → H)
    (T : K → Q → H) (k dk : E → K)
    (q r : E → Q) (v : E) : Prop :=
  (∫ x, inner ℂ (J (fderiv ℝ q x v)) (T (k x) (r x)) ∂ν) +
    (∫ x, inner ℂ (T (k x) (q x)) (J (fderiv ℝ r x v)) ∂ν) =
    -(∫ x, inner ℂ (J (q x)) (T (dk x) (r x)) ∂ν)

omit [FiniteDimensional ℝ E] [BorelSpace E] [NormedSpace ℂ Q]
  [IsScalarTower ℝ ℂ Q] [NormedAddCommGroup K] [NormedSpace ℝ K] in
theorem pairing_congr_field {ν : Measure E} {J : Q → H}
    {T U : K → Q → H} {k dk : E → K} {q r : E → Q} {v : E}
    (h : ProductPairing ν J T k dk q r v) (hTU : T = U) :
    ProductPairing ν J U k dk q r v := hTU ▸ h

/-- Restrict the fixed graph inclusion before specializing to a physical
Fock space, so the scalar restriction is performed in the generic space. -/
theorem complex_smooth_pairing (ν : Measure E) [IsAddHaarMeasure ν]
    (J : Q →L[ℂ] H) (T : K →L[ℝ] Q →L[ℝ] H)
    (hsym : ∀ k q r, inner ℂ (T k q) (J r) = inner ℂ (J q) (T k r))
    (k dk : E → K) (hk : Continuous k) (hdk : Continuous dk) (v : E)
    (hderiv : ∀ x, HasLineDerivAt ℝ k (dk x) x v)
    (q r : E → Q) (hq : ContDiff ℝ ∞ q) (hr : ContDiff ℝ ∞ r)
    (hsq : HasCompactSupport q) (hsr : HasCompactSupport r) :
    ProductPairing ν (fun q => J q) (fun k q => T k q) k dk q r v := by
  exact PauliMagneticWeakDerivative.smooth_pairing ν (J.restrictScalars ℝ) T
    hsym k dk hk hdk v hderiv q r hq hr hsq hsr

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup K] [NormedSpace ℝ K] in
theorem fderiv_map_apply (J : Q →L[ℂ] H) (q : E → Q) (x v : E)
    (hq : DifferentiableAt ℝ q x) :
    fderiv ℝ (fun y => J (q y)) x v = J (fderiv ℝ q x v) := by
  exact congrArg (fun L : E →L[ℝ] H => L v)
    ((J.restrictScalars ℝ).hasFDerivAt.comp x hq.hasFDerivAt).fderiv

end ComplexField

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

attribute [local instance]
  PfHk.PhysicalFormProductRules.instInnerProductSpaceRealSubtypePreLpNatSectorPhotonModePhotonMeasureMemAddSubgroupPhotonFock_pfHk

local instance weakCoreRadiationComplex : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace
local instance weakCoreRadiationReal : NormedSpace ℝ RadiationGraphSpace :=
  NormedSpace.restrictScalars ℝ ℂ RadiationGraphSpace

attribute [local irreducible] radiationRoot weightedKernelSubspace kernelField
  radiationGraphInclusion radiationGraphDerivative

set_option maxHeartbeats 100000 in
/-- The physical weak field product rule for an arbitrary continuously
varying weighted kernel with its first directional derivative. -/
theorem field_smooth_pairing {I : Type} [Fintype I] [DecidableEq I]
    (C : CanonicalSectorCCR photonMeasure)
    (k dk : Position I → WeightedPhotonKernel) (hk : Continuous k) (hdk : Continuous dk)
    (v : Position I) (hderiv : ∀ x, HasLineDerivAt ℝ k (dk x) x v)
    (q r : Position I → RadiationGraphSpace)
    (hq : ContDiff ℝ ∞ q) (hr : ContDiff ℝ ∞ r)
    (hsq : HasCompactSupport q) (hsr : HasCompactSupport r) :
    ProductPairing (E := Position I) (Q := RadiationGraphSpace)
      (K := WeightedPhotonKernel) (H := PhotonFock)
      volume (fun q => radiationGraphInclusion q) (fun k q => kernelField C k q)
      k dk q r v := by
  have h := complex_smooth_pairing
    (E := Position I) (Q := RadiationGraphSpace)
    (K := WeightedPhotonKernel) (H := PhotonFock) volume
    radiationGraphInclusion (PhysicalFormProductRules.fieldBilinear C)
    (fun (k : WeightedPhotonKernel) (q r : RadiationGraphSpace) => by
      exact (congrArg (fun z : PhotonFock => inner ℂ (E := PhotonFock) z
        (radiationGraphInclusion r)) (PhysicalFormProductRules.fieldBilinear_apply C k q)).trans
          ((kernelField_symmetric C k q r).trans
            (congrArg (fun z : PhotonFock => inner ℂ (E := PhotonFock)
              (radiationGraphInclusion q) z)
                (PhysicalFormProductRules.fieldBilinear_apply C k r)).symm))
    k dk hk hdk v hderiv q r hq hr hsq hsr
  have hT : (fun (k : WeightedPhotonKernel) (q : RadiationGraphSpace) =>
      PhysicalFormProductRules.fieldBilinear C k q) =
      (fun (k : WeightedPhotonKernel) (q : RadiationGraphSpace) => kernelField C k q) :=
    funext (fun k => funext (fun q => PhysicalFormProductRules.fieldBilinear_apply C k q))
  exact pairing_congr_field (E := Position I) (Q := RadiationGraphSpace)
    (K := WeightedPhotonKernel) (H := PhotonFock) h hT

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

theorem coupling_smooth_pairing
    (j : Fin N × Fin 3) (v : Configuration N)
    (q r : Configuration N → RadiationGraphSpace)
    (hq : ContDiff ℝ ∞ q) (hr : ContDiff ℝ ∞ r)
    (hsq : HasCompactSupport q) (hsr : HasCompactSupport r) :
    ProductPairing (E := Configuration N) (Q := RadiationGraphSpace)
      (K := WeightedPhotonKernel) (H := PhotonFock)
      volume (fun q => radiationGraphInclusion q) (fun k q => kernelField C k q)
      (RadialGauge.couplingKernel F χ e j)
      (RadialGauge.couplingDerivative F χ hUV e j v) q r v :=
  field_smooth_pairing (I := Fin N × Fin 3) C
    (RadialGauge.couplingKernel F χ e j)
    (RadialGauge.couplingDerivative F χ hUV e j v)
    (RadialGauge.couplingKernel_continuous F χ e j)
    (RadialGauge.couplingDerivative_continuous F χ hUV e j v) v
    (RadialGauge.couplingKernel_hasLineDerivAt F χ hUV e j v)
    q r hq hr hsq hsr

theorem smoothCore_pairing {s t : Set (Configuration N)}
    (a : SmoothCore s) (b : SmoothCore t) (j : Fin N × Fin 3) (v : Configuration N) :
    ProductPairing (E := Configuration N) (Q := RadiationGraphSpace)
      (K := WeightedPhotonKernel) (H := PhotonFock)
      volume (fun q => radiationGraphInclusion q) (fun k q => kernelField C k q)
      (RadialGauge.couplingKernel F χ e j)
      (RadialGauge.couplingDerivative F χ hUV e j v) a.rootWave b.rootWave v :=
  coupling_smooth_pairing F χ hUV C e j v a.rootWave b.rootWave
    a.rootWave_smooth b.rootWave_smooth a.rootWave_compact b.rootWave_compact

end PfHk.PauliMagneticWeakCore


attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
