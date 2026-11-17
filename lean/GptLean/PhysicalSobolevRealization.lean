import GptLean.PhysicalOnePhotonFourier
import GptLean.PhysicalMultiplicationGraph
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
The negative half-Sobolev realization uses the actual one-photon Fourier
transform. Multipliers are extensions of multiplication on smooth compact
test functions. Compatibility on the full common domain follows from
joint graph density and closedness, rather than a matching hypothesis.

The named analytic background below consists of the universal test
integrability, test density, and homogeneous Sobolev multiplier theorem.
It mentions no physical kernel, state, channel, or localization sequence.
-/

noncomputable section

namespace GptLean.PhysicalSobolevRealization

open MeasureTheory Filter Topology PhysicalFock PhysicalOnePhotonFourier
  PhotonLocalizationPhysicalKernels Gaussian
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
set_option Elab.async false

abbrev MomentumSpace := Lp ℂ 2 photonMeasure

def tests : Submodule ℝ (FieldSpace → Polarization) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' _c _f hf := ⟨contDiff_const.smul hf.1, hf.2.smul_left⟩

theorem test_memLp (f : tests) : MemLp (f : FieldSpace → Polarization) 2 volume :=
  f.property.1.continuous.memLp_of_hasCompactSupport f.property.2

def position : tests →ₗ[ℝ] PositionSpace where
  toFun f := (test_memLp f).toLp f.val
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(test_memLp (f + g)).coeFn_toLp, (test_memLp f).coeFn_toLp,
      (test_memLp g).coeFn_toLp, Lp.coeFn_add ((test_memLp f).toLp f.val) ((test_memLp g).toLp g.val)]
      with x h₁ h₂ h₃ h₄
    exact h₁.trans (h₄.trans (congrArg₂ (· + ·) h₂ h₃)).symm
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(test_memLp (c • f)).coeFn_toLp, (test_memLp f).coeFn_toLp,
      Lp.coeFn_smul c ((test_memLp f).toLp f.val)] with x h₁ h₂ h₃
    exact h₁.trans (h₃.trans (congrArg (c • ·) h₂)).symm

theorem position_ae (f : tests) : position f =ᵐ[volume] (f : FieldSpace → Polarization) :=
  (test_memLp f).coeFn_toLp

private theorem multiplyTest_mem (χ : FieldSpace → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (f : tests) :
    (fun y => χ y • f.val y) ∈ tests := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y • f.val y) ∧
    HasCompactSupport (fun y => χ y • f.val y)
  exact ⟨hχ.smul f.property.1,
    HasCompactSupport.smul_left (f := χ) (f' := f.val) f.property.2⟩

def multiplyTest (χ : FieldSpace → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) : tests →ₗ[ℝ] tests where
  toFun f := ⟨fun y => χ y • f.val y, multiplyTest_mem χ hχ f⟩
  map_add' f g := Subtype.ext (funext fun y => smul_add (χ y) (f.val y) (g.val y))
  map_smul' c f := Subtype.ext (funext fun y => smul_comm (χ y) c (f.val y))

@[simp] theorem multiplyTest_apply (χ : FieldSpace → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (f : tests) (y : FieldSpace) :
    (multiplyTest χ hχ f).val y = χ y • f.val y := rfl

def negativeFunction (f : tests) (p : FieldSpace × Fin 2) : ℂ :=
  (Real.sqrt ‖p.1‖)⁻¹ • fourier (position f) p

def representative (a : PositionSpace) (w : MomentumSpace) : Prop :=
  (fourier a, w) ∈ PhysicalMultiplicationGraph.graph photonMeasure
    (fun p => (((Real.sqrt ‖p.1‖)⁻¹ : ℝ) : ℂ))

theorem representative_iff (a : PositionSpace) (w : MomentumSpace) :
    representative a w ↔ w =ᵐ[photonMeasure]
      fun p => (Real.sqrt ‖p.1‖)⁻¹ • fourier a p := by
  change (∀ᵐ p ∂photonMeasure, w p = (((Real.sqrt ‖p.1‖)⁻¹ : ℝ) : ℂ) • fourier a p) ↔ _
  simp only [Complex.coe_smul]
  rfl

theorem representative_closed : IsClosed {aw : PositionSpace × MomentumSpace |
    representative aw.1 aw.2} :=
  (PhysicalMultiplicationGraph.graph_closed photonMeasure
    (H := ℂ) (fun p => (((Real.sqrt ‖p.1‖)⁻¹ : ℝ) : ℂ))).preimage
      ((fourier.continuous.comp continuous_fst).prodMk continuous_snd)

variable (hmem : ∀ f : tests, MemLp (negativeFunction f) 2 photonMeasure)

def negative : tests →ₗ[ℝ] MomentumSpace where
  toFun f := (hmem f).toLp (negativeFunction f)
  map_add' f g := by
    apply Lp.ext
    have he : fourier (position (f + g)) = fourier (position f) + fourier (position g) := by
      rw [map_add, map_add]
    filter_upwards [(hmem (f + g)).coeFn_toLp, (hmem f).coeFn_toLp,
      (hmem g).coeFn_toLp,
      Lp.coeFn_add ((hmem f).toLp _) ((hmem g).toLp _),
      Lp.coeFn_add (fourier (position f)) (fourier (position g))] with p h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₄, Pi.add_apply, h₂, h₃]
    simp only [negativeFunction, he, h₅, Pi.add_apply, smul_add]
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    have he : fourier (position (c • f)) = c • fourier (position f) := by
      change (fourier.restrictScalars ℝ) (position (c • f)) =
        c • (fourier.restrictScalars ℝ) (position f)
      rw [map_smul, map_smul]
    filter_upwards [(hmem (c • f)).coeFn_toLp, (hmem f).coeFn_toLp,
      Lp.coeFn_smul c ((hmem f).toLp _), Lp.coeFn_smul c (fourier (position f))]
      with p h₁ h₂ h₃ h₄
    rw [h₁, h₃, Pi.smul_apply, h₂]
    simp only [negativeFunction, he, h₄, Pi.smul_apply]
    exact smul_comm _ c _

theorem negative_represents (f : tests) : representative (position f) (negative hmem f) :=
  (representative_iff _ _).mpr (hmem f).coeFn_toLp

def scaled (χ : FieldSpace → ℝ) (R : ℝ) (y : FieldSpace) : ℝ := χ (R⁻¹ • y)

theorem scaled_smooth (χ : FieldSpace → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaled χ R) := by
  exact hχ.comp (ContDiff.const_smul (R⁻¹) (contDiff_id (𝕜 := ℝ)))

/-- Standard homogeneous Sobolev analysis, stated only on the concrete
smooth test functions and their actual Fourier representatives. -/
structure StandardHomogeneousSobolev where
  test_integrability : ∀ f : tests, MemLp (negativeFunction f) 2 photonMeasure
  negative_dense : DenseRange (negative test_integrability)
  joint_dense : ∀ a w, representative a w → ∃ f : ℕ → tests,
    Tendsto (fun n => position (f n)) atTop (𝓝 a) ∧
      Tendsto (fun n => negative test_integrability (f n)) atTop (𝓝 w)
  scaled_bound : ∀ (χ : FieldSpace → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ),
    HasCompactSupport χ → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ f : tests,
      ‖negative test_integrability (multiplyTest (scaled χ R) (scaled_smooth χ hχ R) f)‖ ≤
        C * ‖negative test_integrability f‖

namespace StandardHomogeneousSobolev

variable (B : StandardHomogeneousSobolev)

theorem bound (χ : FieldSpace → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : tests,
      ‖negative B.test_integrability (multiplyTest χ hχ f)‖ ≤
        C * ‖negative B.test_integrability f‖ := by
  obtain ⟨C, hC, h⟩ := B.scaled_bound χ hχ hc
  refine ⟨C, hC, fun f => ?_⟩
  have hs : scaled χ 1 = χ := by
    funext y
    simp only [scaled, inv_one, one_smul]
  simpa only [hs] using h 1 zero_lt_one f

open scoped Classical in
def multiplier (χ : FieldSpace → ℝ) : MomentumSpace →L[ℝ] MomentumSpace :=
  if hχ : ContDiff ℝ (⊤ : ℕ∞) χ then
    ((negative B.test_integrability).comp (multiplyTest χ hχ)).extendOfNorm
      (negative B.test_integrability)
  else 0

theorem multiplier_action (χ : FieldSpace → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (f : tests) :
    B.multiplier χ (negative B.test_integrability f) =
      negative B.test_integrability (multiplyTest χ hχ f) := by
  unfold multiplier
  rw [dite_eq_left hχ]
  apply LinearMap.extendOfNorm_eq B.negative_dense
  obtain ⟨C, _, hC⟩ := B.bound χ hχ hc
  exact ⟨C, hC⟩

theorem multiplier_scaled_bound (χ : FieldSpace → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ‖B.multiplier (scaled χ R)‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := B.scaled_bound χ hχ hc
  refine ⟨C, hC, fun R hR => ?_⟩
  unfold multiplier
  rw [dite_eq_left (scaled_smooth χ hχ R)]
  exact LinearMap.opNorm_extendOfNorm_le B.negative_dense hC (h R hR)

def background : SobolevMultiplierBackground MomentumSpace where
  TestFiber := Polarization
  tests := tests
  compact f := f.property.2
  realize := negative B.test_integrability
  dense := B.negative_dense
  mul_mem χ hχ f := (multiplyTest χ hχ f).property
  multiplier := B.multiplier
  action := B.multiplier_action
  scaled_bound := B.multiplier_scaled_bound

theorem position_multiply (χ : FieldSpace → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχm : AEStronglyMeasurable χ (volume : Measure FieldSpace))
    (hb : ∀ᵐ y ∂(volume : Measure FieldSpace), |χ y| ≤ 1) (f : tests) :
    position (multiplyTest χ hχ f) = PhotonKernelLocalization.l2Multiplier χ hχm hb (position f) := by
  apply Lp.ext
  filter_upwards [position_ae (multiplyTest χ hχ f), position_ae f,
    PhotonKernelLocalization.l2Multiplier_apply_ae χ hχm hb (position f)] with y h₁ h₂ h₃
  exact h₁.trans (h₃.trans (congrArg (χ y • ·) h₂)).symm

/-- The full common-domain identity is a consequence of the concrete
closed graph and the universal smooth test core theorem. -/
theorem multiplier_represents (χ : FieldSpace → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hχm : AEStronglyMeasurable χ (volume : Measure FieldSpace))
    (hb : ∀ᵐ y ∂(volume : Measure FieldSpace), |χ y| ≤ 1)
    (a : PositionSpace) (w : MomentumSpace) (hw : representative a w) :
    representative (PhotonKernelLocalization.l2Multiplier χ hχm hb a) (B.multiplier χ w) := by
  obtain ⟨f, hfa, hfw⟩ := B.joint_dense a w hw
  apply representative_closed.mem_of_tendsto
    (((PhotonKernelLocalization.l2Multiplier χ hχm hb).continuous.tendsto a |>.comp hfa).prodMk_nhds
      ((B.multiplier χ).continuous.tendsto w |>.comp hfw))
  apply Filter.Eventually.of_forall
  intro n
  change representative (PhotonKernelLocalization.l2Multiplier χ hχm hb (position (f n)))
    (B.multiplier χ (negative B.test_integrability (f n)))
  rw [B.multiplier_action χ hχ hc, ← position_multiply χ hχ hχm hb]
  exact negative_represents B.test_integrability _

def identification : MomentumSpace ≃ₗᵢ[ℝ] MomentumSpace := LinearIsometryEquiv.refl ℝ _

theorem fourier_compatibility (χ : FieldSpace → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hχm : AEStronglyMeasurable χ (volume : Measure FieldSpace))
    (hb : ∀ᵐ y ∂(volume : Measure FieldSpace), |χ y| ≤ 1) (a : PositionSpace) (w : MomentumSpace)
    (hw : (coordinates (LinearIsometryEquiv.refl ℂ MomentumSpace)).representative identification a w) :
    (coordinates (LinearIsometryEquiv.refl ℂ MomentumSpace)).representative identification
      (PhotonKernelLocalization.l2Multiplier χ hχm hb a) (B.background.multiplier χ w) := by
  exact (representative_iff _ _).mp (B.multiplier_represents χ hχ hc hχm hb a w
    ((representative_iff _ _).mpr hw))

end StandardHomogeneousSobolev
end GptLean.PhysicalSobolevRealization
