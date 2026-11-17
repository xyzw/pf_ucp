import GptLean.PhysicalPFScalarMultiplier
import PfHk.SmoothCutoffBounds

/-! Arbitrary smooth compact scalar tests on the actual reference domain.
The reference lift is constructed using the existing bounded differentiable
multiplier. No domain-preservation premise is added. -/

noncomputable section
namespace PfHk.PhysicalScalarTests

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.ElectronicH1Multiplier
open scoped InnerProductSpace ContDiff

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Every smooth compactly supported real scalar is a bounded
first-order multiplier, with its literal scalar function. -/
theorem exists_differentiableMultiplier
    (η : EuclideanSpace ℝ I → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) :
    ∃ a : DifferentiableMultiplier I, a.weight = η := by
  obtain ⟨B, hB⟩ := hη.continuous.bounded_above_of_compact_support hs
  obtain ⟨D, hD⟩ := (hη.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hs.fderiv ℝ)
  refine ⟨{
    weight := η
    differentiable := hη.differentiable (by simp)
    bound := B
    bounded := fun x => ?_
    derivativeBound := D
    derivative_bounded := fun i x => ?_ }, rfl⟩
  · simpa only [Real.norm_eq_abs] using hB x
  · simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using
      (fderiv ℝ η x).le_of_opNorm_le (hD x) (EuclideanSpace.single i 1)

def differentiableMultiplier
    (η : EuclideanSpace ℝ I → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) : DifferentiableMultiplier I :=
  Classical.choose (exists_differentiableMultiplier η hη hs)

theorem differentiableMultiplier_weight
    (η : EuclideanSpace ℝ I → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) :
    (differentiableMultiplier η hη hs).weight = η :=
  Classical.choose_spec (exists_differentiableMultiplier η hη hs)

/-- The actual physical reference vector obtained by scalar testing. -/
def testVector (V : Position I → ℝ)
    (η : Position I → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (u : Reference I V) : Reference I V :=
  PhysicalPFScalarMultiplier.multiply V (differentiableMultiplier η hη hs) u

attribute [local irreducible] inclusion PhysicalPFReference.referenceSubspace
  PhysicalPFScalarMultiplier.multiply

theorem inclusion_testVector_ae (V : Position I → ℝ)
    (η : Position I → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (u : Reference I V) :
    (inclusion I V (testVector V η hη hs u) : Position I → PhotonFock) =ᵐ[volume]
      fun X => η X • inclusion I V u X := by
  let a := differentiableMultiplier η hη hs
  have he := PhysicalPFScalarMultiplier.value_multiply V a u
  have ha := PhotonLocalization.realL2Multiplier_apply a.weight
    a.differentiable.continuous.aestronglyMeasurable a.bound
    (Filter.Eventually.of_forall a.bounded) (inclusion I V u)
  filter_upwards [ha] with X hX
  have hvalue : inclusion I V (testVector V η hη hs u) X =
      a.multiplier (inclusion I V u) X :=
    congrArg (fun ψ : WaveSpace I => ψ X) he
  exact hvalue.trans (hX.trans (congrArg (fun r : ℝ => r • inclusion I V u X)
    (congrFun (differentiableMultiplier_weight η hη hs) X)))

section Hilbert

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem re_inner_of_scalar_ae (η : X → ℝ) (z u : Lp H 2 μ)
    (hz : (z : X → H) =ᵐ[μ] fun x => η x • u x) :
    (fun x => (⟪z x, u x⟫_ℂ).re) =ᵐ[μ] fun x => η x * ‖u x‖ ^ 2 := by
  filter_upwards [hz] with x hx
  rw [hx, inner_smul_left_eq_smul, Complex.smul_re, smul_eq_mul]
  exact congrArg (fun r : ℝ => η x * r) (norm_sq_eq_re_inner (𝕜 := ℂ) (u x)).symm

/-- A scalar-weighted physical pair becomes the scalar density test.
This equality only uses almost-everywhere equality of its integrands. -/
theorem weighted_re_inner (η w : X → ℝ) (z u : Lp H 2 μ)
    (hz : (z : X → H) =ᵐ[μ] fun x => η x • u x) :
    (∫ x, w x * (⟪z x, u x⟫_ℂ).re ∂μ) =
      ∫ x, η x * (w x * ‖u x‖ ^ 2) ∂μ := by
  apply integral_congr_ae
  filter_upwards [re_inner_of_scalar_ae η z u hz] with x hx
  rw [hx]
  ring

theorem mass_re_of_scalar_ae (η : X → ℝ) (z u : Lp H 2 μ)
    (hz : (z : X → H) =ᵐ[μ] fun x => η x • u x) :
    (⟪z, u⟫_ℂ).re = ∫ x, η x * ‖u x‖ ^ 2 ∂μ :=
  (congrArg Complex.re (L2.inner_def z u)).trans
    ((integral_re (L2.integrable_inner (𝕜 := ℂ) z u)).symm.trans
      (integral_congr_ae (re_inner_of_scalar_ae η z u hz)))

end Hilbert

omit [DecidableEq I] in
/-- Every smooth compact scalar can test any integrable real density. -/
theorem test_integrable (η : Position I → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (f : Position I → ℝ) (hf : Integrable f volume) :
    Integrable (fun X => η X * f X) volume := by
  obtain ⟨B, hB⟩ := hη.continuous.bounded_above_of_compact_support hs
  exact hf.bdd_mul hη.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hB)

theorem mass_re (V : Position I → ℝ)
    (η : Position I → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (u : Reference I V) :
    (⟪inclusion I V (testVector V η hη hs u), inclusion I V u⟫_ℂ).re =
      ∫ X, η X * ‖inclusion I V u X‖ ^ 2 :=
  mass_re_of_scalar_ae η _ _ (inclusion_testVector_ae V η hη hs u)

theorem weighted_test (V : Position I → ℝ)
    (η : Position I → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (w : Position I → ℝ) (u : Reference I V) :
    (∫ X, w X * (⟪inclusion I V (testVector V η hη hs u) X,
      inclusion I V u X⟫_ℂ).re) = ∫ X, η X * (w X * ‖inclusion I V u X‖ ^ 2) :=
  weighted_re_inner η w _ _ (inclusion_testVector_ae V η hη hs u)

end PfHk.PhysicalScalarTests
