import PfHk.CenteredPhysicalPolarForm
import PfHk.CenteredRadialGaugeRadialCore

/-! Support of the actual original physical form-core vector and its
first covariant derivatives. These facts localize the weak polar identity
to a compact cylinder slab before the dense test argument. -/

noncomputable section
namespace PfHk.CenteredPhysicalReference

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain
  PfHk.CenteredRadialGauge
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
local instance supportCorePhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] kernelField radiationGraphInclusion radiationGraphDerivative
  fullRootProjection fullRadiationInclusion coreValue

private theorem map_fderiv_zero {E H K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (T : H →L[ℝ] K) (f : E → H) {x : E} (hx : x ∉ tsupport f) (v : E) :
    T (fderiv ℝ f x v) = 0 := by
  rw [fderiv_of_notMem_tsupport ℝ hx]
  exact map_zero T

variable {N : ℕ} {s : Set (Configuration N)} (a : SmoothCore s)

theorem rootWave_eq_zero_of_notMem {X : Configuration N} (hX : X ∉ s) : a.rootWave X = 0 := by
  have hx : X ∉ tsupport a.representative := fun h => hX (a.support h)
  exact (congrArg fullRootProjection (image_eq_zero_of_notMem_tsupport hx)).trans (map_zero _)

theorem coreValue_fderiv_eq_zero_of_notMem {X : Configuration N} (hX : X ∉ s) (v : Configuration N) :
    fderiv ℝ (coreValue a.rootWave) X v = 0 := by
  have hx : X ∉ tsupport a.representative := fun h => hX (a.support h)
  have he : coreValue a.rootWave = (fun q : FullRadiationGraph => fullRadiationInclusion q) ∘ a.representative := by
    funext Y
    unfold coreValue SmoothCore.rootWave fullRadiationInclusion
    rfl
  have hsub : tsupport (coreValue a.rootWave) ⊆ tsupport a.representative := by
    rw [he]
    exact tsupport_comp_subset (map_zero fullRadiationInclusion) a.representative
  have hd := fderiv_of_notMem_tsupport ℝ (fun h => hx (hsub h))
  exact congrArg (fun L : Configuration N →L[ℝ] PhotonFock => L v) hd

variable (F : Frame) (χ : ArticleCutoff) (e : ℝ) (O : Configuration N)
  (C : CanonicalSectorCCR photonMeasure)

theorem coreCovariant_eq_zero_of_notMem {X : Configuration N} (hX : X ∉ s) (j : Fin N × Fin 3) :
    coreCovariant F χ e O C a.rootWave j X = 0 := by
  unfold coreCovariant
  rw [coreValue_fderiv_eq_zero_of_notMem a hX, rootWave_eq_zero_of_notMem a hX, map_zero,
    smul_zero, zero_add]

theorem physicalFormDensity_zero_left (q : Configuration N → RadiationGraphSpace)
    {X : Configuration N} (hX : X ∉ s) : physicalFormDensity F χ O C e a.rootWave q X = 0 := by
  unfold physicalFormDensity
  simp only [coreCovariant_eq_zero_of_notMem a F χ e O C hX, inner_zero_left, Finset.sum_const_zero,
    rootWave_eq_zero_of_notMem a hX, map_zero, mul_zero, zero_add]

end PfHk.CenteredPhysicalReference
