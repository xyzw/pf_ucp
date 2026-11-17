import PfHk.PhysicalScalarFormDifference
import PfHk.PhysicalScalarTests
import PfHk.PhysicalScalarUniqueness

/-! Scalar-potential uniqueness from two actual physical weak equations.
Smooth scalar multiples of the common reference vector are admissible tests.
Subtraction and nonvanishing determine the exact one-body constant. -/

noncomputable section
namespace PfHk.PhysicalScalarWeakUniqueness

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.PhysicalScalarFormDifference
open scoped InnerProductSpace ContDiff

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 150000

private theorem real_eigen_re (E : ℝ) {a b : ℂ} (h : a = (E : ℂ) * b) :
    a.re = E * b.re := by
  rw [h]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem eigen_difference (a₁ a₂ m E₁ E₂ : ℝ)
    (h₁ : a₁ = E₁ * m) (h₂ : a₂ = E₂ * m) :
    a₁ - a₂ = (E₁ - E₂) * m := by
  rw [h₁, h₂]
  ring

private theorem shifted_density_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f ρ : X → ℝ) (E : ℝ)
    (hf : Integrable (fun x => f x * ρ x) μ) (hρ : Integrable ρ μ) :
    Integrable (fun x => (f x - E) * ρ x) μ :=
  (hf.sub (hρ.const_mul E)).congr
    (Filter.Eventually.of_forall fun x => (sub_mul (f x) E (ρ x)).symm)

private theorem shifted_test_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (η f ρ : X → ℝ) (E : ℝ)
    (hf : Integrable (fun x => η x * (f x * ρ x)) μ)
    (hρ : Integrable (fun x => η x * ρ x) μ)
    (he : (∫ x, η x * (f x * ρ x) ∂μ) = E * ∫ x, η x * ρ x ∂μ) :
    (∫ x, η x * ((f x - E) * ρ x) ∂μ) = 0 := by
  calc
    _ = ∫ x, η x * (f x * ρ x) - E * (η x * ρ x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = (∫ x, η x * (f x * ρ x) ∂μ) - E * ∫ x, η x * ρ x ∂μ := by
      rw [integral_sub hf (hρ.const_mul E), integral_const_mul]
    _ = 0 := by rw [he, sub_self]

attribute [local irreducible] inclusion covariant radiation potential roughMultiply
  PhysicalPFReference.referenceSubspace externalForm scalarDifference

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ j, AEStronglyMeasurable (κ j) volume)
  (M : ℝ) (hb : ∀ j, ∀ᵐ X ∂volume, ‖κ j X‖ ≤ M) (e : ℝ)
  (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

set_option hygiene false in
local notation "D₁" => externalDomain (N := N) A₁ v₁ c hc
set_option hygiene false in
local notation "D₂" => externalDomain (N := N) A₂ v₂ c hc

/-- Subtracting the physical weak equations determines the scalar
potential up to the exact energy difference divided by particle number.
All multiplier domains and scalar distribution identities are derived. -/
theorem potential_difference_constant (hN : 0 < N) (E₁ E₂ : ℝ) (u : Ref N)
    (hA : A₁.val =ᵐ[volume] A₂.val)
    (h₁ : IsExternalWeakEigenstate (fun _ => 0) C κ hκ M hb e
      (vector A₁) (positive v₁ c) (negative v₁ c) E₁ u (D₁ u))
    (h₂ : IsExternalWeakEigenstate (fun _ => 0) C κ hκ M hb e
      (vector A₂) (positive v₂ c) (negative v₂ c) E₂ u (D₂ u))
    (hu : ∀ᵐ X ∂volume, inclusion (Fin N × Fin 3) (fun _ => 0) u X ≠ 0) :
    ∀ᵐ x ∂volume, v₁.val x = v₂.val x + (E₁ - E₂) / N := by
  let ψ : WaveSpace (Fin N × Fin 3) := inclusion (Fin N × Fin 3) (fun _ => 0) u
  let f : PhysicalSourceCoordinates.Configuration N → ℝ := scalarDifference (N := N) v₁ v₂
  let ρ : PhysicalSourceCoordinates.Configuration N → ℝ := fun X => ‖ψ X‖ ^ 2
  have hf : Integrable (fun X => f X * ρ X) volume := density_integrable (N := N) v₁ v₂ u
  have hρ : Integrable ρ volume := (Lp.memLp ψ).norm.integrable_sq
  have hn : ∀ᵐ X ∂volume, ρ X ≠ 0 :=
    hu.mono fun X hX => pow_ne_zero 2 (norm_ne_zero_iff.mpr hX)
  have hi := shifted_density_integrable volume f ρ (E₁ - E₂) hf hρ
  have htest : ∀ η : PhysicalSourceCoordinates.Configuration N → ℝ,
      ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ X, η X * ((f X - (E₁ - E₂)) * ρ X) = 0 := by
    intro η hη hs
    let z : Ref N := PhysicalScalarTests.testVector (fun _ => 0) η hη hs u
    have hd := difference (N := N) C κ hκ M hb e A₁ A₂ v₁ v₂ c hc hA z u
    have hw := PhysicalScalarTests.weighted_test (fun _ => 0) η hη hs f u
    have hm := PhysicalScalarTests.mass_re (fun _ => 0) η hη hs u
    have he₁ := real_eigen_re E₁ (h₁ z (D₁ z))
    have he₂ := real_eigen_re E₂ (h₂ z (D₂ z))
    have he : (∫ X, η X * (f X * ρ X)) = (E₁ - E₂) * ∫ X, η X * ρ X :=
      hw.symm.trans (hd.symm.trans
        ((eigen_difference _ _ _ E₁ E₂ he₁ he₂).trans
          (congrArg (fun m : ℝ => (E₁ - E₂) * m) hm)))
    exact shifted_test_zero volume η f ρ (E₁ - E₂)
      (PhysicalScalarTests.test_integrable η hη hs (fun X => f X * ρ X) hf)
      (PhysicalScalarTests.test_integrable η hη hs ρ hρ) he
  have hz := PhysicalScalarUniqueness.ae_eq_zero_of_weak_weight volume
    (fun X => f X - (E₁ - E₂)) ρ hn hi htest
  apply PhysicalScalarUniqueness.potential_difference_constant_of_sum_eq hN
    (v₁.val : PhysicalPairSpace.Position → ℝ) (v₂.val : PhysicalPairSpace.Position → ℝ) E₁ E₂
  filter_upwards [hz] with X hX
  exact (scalarDifference_eq_sum_particle (N := N) v₁ v₂ X).symm.trans (sub_eq_zero.mp hX)

end PfHk.PhysicalScalarWeakUniqueness
