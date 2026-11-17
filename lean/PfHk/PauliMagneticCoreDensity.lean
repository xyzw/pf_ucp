import PfHk.WeylCoreReference

/-! Ordinary smooth radiation-graph core approximation is the zero-label
case of the retained, coefficient-independent Weyl form-core theorem. -/

noncomputable section
namespace PfHk.PauliMagneticCoreDensity

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalWeyl GptLean.Representability PfHk.PhysicalOperatorDomain
  PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
open scoped Topology ContDiff

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

attribute [local irreducible] radiationRoot weightedKernelSubspace
  PhysicalPFReference.referenceSubspace radiationGraphInclusion fullRootProjection
  fullRadiationInclusion

variable {I : Type} [Fintype I] [DecidableEq I]
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)

omit [Fintype I] [DecidableEq I] in
private theorem zero_match (_x : Position I) :
    ∀ᵐ p ∂photonMeasure, (0 : Lp ℂ 2 photonMeasure) p =
      (Real.sqrt ‖p.1‖ : ℂ) * (0 : WeightedPhotonKernel).val.1 p := by
  filter_upwards [Lp.coeFn_zero ℂ 2 photonMeasure] with p hp
  change (0 : Lp ℂ 2 photonMeasure) p =
    (Real.sqrt ‖p.1‖ : ℂ) * (0 : Lp ℂ 2 photonMeasure) p
  simp only [hp, Pi.zero_apply, mul_zero]

theorem zero_reference {s : Set (Position I)} (a : SmoothCore s) :
    WeylCoreReference.reference (I := I) W B (fun _ : Position I => 0) contDiff_const
      (fun _ : Position I => 0) continuous_const (zero_match (I := I)) a = a.reference := by
  have hg : WeylCoreReference.graph (I := I) W (fun _ : Position I => 0)
      (fun _ : Position I => 0) (zero_match (I := I)) a = a.rootWave := by
    funext x
    apply radiationGraphInclusion_injective_weyl
    have hv : radiationGraphInclusion (a.rootWave x) =
        fullRadiationInclusion (a.representative x) := by
      unfold SmoothCore.rootWave fullRadiationInclusion
      rfl
    have hw : W.weyl (0 : Lp ℂ 2 photonMeasure)
        (fullRadiationInclusion (a.representative x)) =
        fullRadiationInclusion (a.representative x) :=
      congrArg (fun T : PhotonFock ≃ₗᵢ[ℂ] PhotonFock =>
      T (fullRadiationInclusion (a.representative x))) W.zero
    exact (WeylCoreReference.graph_inclusion (I := I) W
      (fun _ : Position I => 0) (fun _ : Position I => 0)
      (zero_match (I := I)) a x).trans (hw.trans hv.symm)
  unfold WeylCoreReference.reference SmoothCore.reference
  congr 1

theorem approximate (D : StandardWeylFormCoreDensity W B)
    (s : Set (Position I)) (hs : IsOpen s) (u : Reference I (fun _ => 0))
    (hu : CompactlySupportedIn s u) :
    ∃ a : ℕ → SmoothCore s, Tendsto (fun n => (a n).reference) atTop (𝓝 u) := by
  let h : Position I → WeightedPhotonKernel := fun _ => 0
  let y : Position I → Lp ℂ 2 photonMeasure := fun _ => 0
  have hc : ContDiff ℝ (1 : ℕ∞) h := contDiff_const
  have hyc : Continuous y := continuous_const
  have hy : ∀ x, ∀ᵐ p ∂photonMeasure,
      y x p = (Real.sqrt ‖p.1‖ : ℂ) * (h x).val.1 p := zero_match (I := I)
  have hd : ∃ a : ℕ → SmoothCore s,
      Tendsto (fun n => WeylCoreReference.reference (I := I) W B h hc y hyc hy (a n))
        atTop (𝓝 u) :=
    @StandardWeylFormCoreDensity.approximate W B D I _ _ h hc y hyc hy s hs u hu
  obtain ⟨a, ha⟩ := hd
  refine ⟨a, ?_⟩
  have he (n : ℕ) :
      WeylCoreReference.reference (I := I) W B h hc y hyc hy (a n) = (a n).reference :=
    zero_reference (I := I) W B (a n)
  exact Filter.Tendsto.congr he ha

end PfHk.PauliMagneticCoreDensity

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
