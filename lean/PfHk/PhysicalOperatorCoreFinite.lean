import PfHk.PhysicalOperatorCore

/-! Finite photon-number support is retained by ordinary derivatives of
the graph-smooth electronic core. -/

noncomputable section
namespace PfHk.PhysicalOperatorDomain

open GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.Representability

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
set_option Elab.async false

private theorem linear_fderiv_zero {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : F →L[ℝ] G) (f : E → F) (hf : Differentiable ℝ f)
    (hzero : ∀ x, T (f x) = 0) (x v : E) : T (fderiv ℝ f x v) = 0 := by
  have hcomp := (T.hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv
  have hz : fderiv ℝ (fun y => T (f y)) x = 0 := by
    rw [show (fun y => T (f y)) = (fun _ => 0) from funext hzero]
    exact fderiv_const_apply 0
  exact congrArg (fun K : E →L[ℝ] G => K v) (hcomp.symm.trans hz)

private theorem complex_linear_fderiv_zero {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
    [IsScalarTower ℝ ℂ G]
    (T : F →L[ℂ] G) (f : E → F) (hf : Differentiable ℝ f)
    (hzero : ∀ x, T (f x) = 0) (x v : E) : T (fderiv ℝ f x v) = 0 :=
  linear_fderiv_zero (T.restrictScalars ℝ) f hf hzero x v

attribute [local irreducible] fullRadiationSubmodule fullRootProjection
  fullRadiationOutput fullRadiationInclusion ContDiff

variable {I : Type} [Fintype I] [DecidableEq I]

theorem SmoothCore.derivative_photonFinite {s : Set (Position I)} (a : SmoothCore s)
    (x v : Position I) : FiniteNumberSupport photonMeasure a.photonCutoff
      (fullRadiationInclusion (fderiv ℝ a.representative x v)) := by
  intro n hn
  let T : FullRadiationGraph →L[ℂ] Sector photonMeasure n :=
    (lp.evalCLM ℂ (Sector photonMeasure) 2 n).comp fullRadiationInclusion
  exact complex_linear_fderiv_zero T a.representative
    (a.smooth.differentiable (by simp)) (fun y => a.photonFinite y n hn) x v

/-- A single field changes photon number by at most one. This is proved
from its actual creation and annihilation coordinates. -/
theorem kernelField_photonFinite (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) (M : ℕ)
    (hq : FiniteNumberSupport photonMeasure M (radiationGraphInclusion q)) :
    FiniteNumberSupport photonMeasure (M + 1) (kernelField C k q) := by
  intro n hn
  have ha : kernelAnnihilation k q n = 0 := by
    change annihilationSector photonMeasure n k.val.1
      (radiationGraphInclusion q (n + 1)) = 0
    rw [hq (n + 1) (by omega), map_zero]
  have hc : kernelCreation C k q n = 0 := by
    cases n with
    | zero => rfl
    | succ n =>
      change creationSector photonMeasure n k.val.1 (radiationGraphInclusion q n) = 0
      rw [hq n (by omega), map_zero]
  change kernelAnnihilation k q n + kernelCreation C k q n = 0
  rw [ha, hc, zero_add]

end PfHk.PhysicalOperatorDomain
