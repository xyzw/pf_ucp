import PfHk.PauliScalarFormDifference
import PfHk.PhysicalScalarTests
import PfHk.PhysicalScalarUniqueness
import PfHk.PauliFermionicReduction

/-! Scalar uniqueness for the coupled Pauli weak equations. Smooth
scalar tests are applied to every component of the same spinor. No
individual spin component is assumed to solve an eigenvalue equation. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliScalarWeakUniqueness

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.PauliGroundState PfHk.PauliSpin PfHk.CenteredPhysicalReference
open scoped ContDiff

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 70000

attribute [local irreducible] referenceSubspace inclusion covariant radiation
  roughMultiply externalCovariant rawForm PauliGroundState.energy

private theorem finite_weight_integral {S X : Type*} [Fintype S] [MeasurableSpace X]
    (μ : Measure X) (w : X → ℝ) (f : S → X → ℝ)
    (h : ∀ s, Integrable (fun x => w x * f s x) μ) :
    (∫ x, w x * (∑ s, f s x) ∂μ) = ∑ s, ∫ x, w x * f s x ∂μ := by
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun s _ => h s)

private theorem finite_weight_integrable {S X : Type*} [Fintype S] [MeasurableSpace X]
    (μ : Measure X) (w : X → ℝ) (f : S → X → ℝ)
    (h : ∀ s, Integrable (fun x => w x * f s x) μ) :
    Integrable (fun x => w x * (∑ s, f s x)) μ := by
  simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun s _ => h s)

variable {N : ℕ}
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hb : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

set_option hygiene false in
local notation "D₁" => physicalDomain (N := N) A₁ v₁ c hc
set_option hygiene false in
local notation "D₂" => physicalDomain (N := N) A₂ v₂ c hc

theorem potential_difference_constant (hN : 0 < N) (E₁ E₂ : ℝ) (u : Ref N)
    (hA : A₁.val =ᵐ[volume] A₂.val)
    (h₁ : IsWeakEigenstate C κ hκ M hb e (vector A₁) (positive v₁ c) (negative v₁ c)
      E₁ u (D₁ u))
    (h₂ : IsWeakEigenstate C κ hκ M hb e (vector A₂) (positive v₂ c) (negative v₂ c)
      E₂ u (D₂ u))
    (hu : ∀ᵐ X ∂volume, PauliReference.wave u X ≠ 0) :
    ∀ᵐ x ∂volume, v₁.val x = v₂.val x + (E₁ - E₂) / N := by
  let f : Configuration N → ℝ := PhysicalScalarFormDifference.scalarDifference v₁ v₂
  let d : SpinIndex N → Configuration N → ℝ :=
    fun s X => ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2
  let ρ : Configuration N → ℝ := fun X => ∑ s, d s X
  have hi (s : SpinIndex N) : Integrable (fun X => f X * d s X) volume :=
    PhysicalScalarFormDifference.density_integrable v₁ v₂ (u s)
  have hdi (s : SpinIndex N) : Integrable (d s) volume :=
    (Lp.memLp (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))).norm.integrable_sq
  have hf : Integrable (fun X => f X * ρ X) volume :=
    finite_weight_integrable volume f d hi
  have hρ : Integrable ρ volume := integrable_finsetSum _ (fun s _ => hdi s)
  have hn : ∀ᵐ X ∂volume, ρ X ≠ 0 := by
    filter_upwards [hu, PauliReference.wave_norm_sq_ae u] with X hX hnorm
    intro hz
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hX) (hnorm.trans hz)
  have hshift : Integrable (fun X => (f X - (E₁ - E₂)) * ρ X) volume :=
    (hf.sub (hρ.const_mul (E₁ - E₂))).congr
      (Filter.Eventually.of_forall fun X => (sub_mul _ _ _).symm)
  have htest : ∀ η : Configuration N → ℝ,
      ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ X, η X * ((f X - (E₁ - E₂)) * ρ X) = 0 := by
    intro η hη hs
    let z : Ref N := fun s => PhysicalScalarTests.testVector (fun _ => 0) η hη hs (u s)
    have hid (s : SpinIndex N) : Integrable (fun X => η X * d s X) volume :=
      PhysicalScalarTests.test_integrable η hη hs (d s) (hdi s)
    have hif (s : SpinIndex N) : Integrable (fun X => η X * (f X * d s X)) volume :=
      PhysicalScalarTests.test_integrable η hη hs (fun X => f X * d s X) (hi s)
    have hmi : (∫ X, η X * ρ X) = ∑ s, ∫ X, η X * d s X :=
      finite_weight_integral volume η d hid
    have hfi : (∫ X, η X * (f X * ρ X)) = ∑ s, ∫ X, η X * (f X * d s X) := by
      have hh := finite_weight_integral volume (fun X => η X * f X) d
        (fun s => (hif s).congr (Filter.Eventually.of_forall fun X => (mul_assoc _ _ _).symm))
      simpa only [mul_assoc] using hh
    have hm : (mass z u).re = ∫ X, η X * ρ X := by
      unfold mass
      rw [Complex.re_sum]
      exact (Finset.sum_congr rfl (fun s _ =>
        PhysicalScalarTests.mass_re (fun _ => 0) η hη hs (u s))).trans hmi.symm
    have hd :
        (rawForm C κ hκ M hb e (vector A₁) (positive v₁ c) (negative v₁ c)
          z u (D₁ z) (D₁ u)).re -
        (rawForm C κ hκ M hb e (vector A₂) (positive v₂ c) (negative v₂ c)
          z u (D₂ z) (D₂ u)).re = ∫ X, η X * (f X * ρ X) :=
      (PauliScalarFormDifference.difference C κ hκ M hb e A₁ A₂ v₁ v₂ c hc hA z u).trans
        ((Finset.sum_congr rfl (fun s _ =>
          PhysicalScalarTests.weighted_test (fun _ => 0) η hη hs f (u s))).trans hfi.symm)
    have he₁ := congrArg Complex.re (h₁ z (D₁ z))
    have he₂ := congrArg Complex.re (h₂ z (D₂ z))
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at he₁ he₂
    have he : (∫ X, η X * (f X * ρ X)) = (E₁ - E₂) * ∫ X, η X * ρ X := by
      rw [← hd, he₁, he₂, hm]
      ring
    have hiηf := PhysicalScalarTests.test_integrable η hη hs (fun X => f X * ρ X) hf
    have hiηρ := PhysicalScalarTests.test_integrable η hη hs ρ hρ
    calc
      _ = ∫ X, η X * (f X * ρ X) - (E₁ - E₂) * (η X * ρ X) :=
        integral_congr_ae (Filter.Eventually.of_forall fun X => by ring)
      _ = (∫ X, η X * (f X * ρ X)) - (E₁ - E₂) * ∫ X, η X * ρ X := by
        rw [integral_sub hiηf (hiηρ.const_mul (E₁ - E₂)), integral_const_mul]
      _ = 0 := by rw [he, sub_self]
  have hz := PhysicalScalarUniqueness.ae_eq_zero_of_weak_weight volume
    (fun X => f X - (E₁ - E₂)) ρ hn hshift htest
  apply PhysicalScalarUniqueness.potential_difference_constant_of_sum_eq hN
    (v₁.val : PhysicalPairSpace.Position → ℝ) (v₂.val : PhysicalPairSpace.Position → ℝ) E₁ E₂
  filter_upwards [hz] with X hX
  exact (PhysicalScalarFormDifference.scalarDifference_eq_sum_particle v₁ v₂ X).symm.trans
    (sub_eq_zero.mp hX)

end PfHk.PauliScalarWeakUniqueness

namespace PfHk.PauliHohenbergKohn

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  PfHk.PauliGroundState PfHk.CenteredPhysicalReference PfHk.PhysicalCommonFormDomain

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000
attribute [local irreducible] referenceSubspace inclusion PauliGroundState.energy

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (F : Frame) (χ : ArticleCutoff)

theorem scalar_of_common_ground_state (hN : 0 < N)
    (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (p : State N)
    (h₁ : IsGroundState C e F χ A₁ v₁ c hc p)
    (h₂ : IsGroundState C e F χ A₂ v₂ c hc p)
    (hA : A₁.val =ᵐ[volume] A₂.val)
    (hn : ∀ᵐ X ∂volume, PauliReference.wave p.vector X ≠ 0) :
    ∀ᵐ x ∂volume, v₁.val x = v₂.val x +
      (energy C e F χ A₁ v₁ c hc p.vector - energy C e F χ A₂ v₂ c hc p.vector) / N :=
  PauliScalarWeakUniqueness.potential_difference_constant
    C (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ)
    (profile_bound F χ 0) e A₁ A₂ v₁ v₂ c hc hN _ _ p.vector hA
    (PauliGroundStateWeak.full_weak_equation C e F χ A₁ v₁ c hc p h₁)
    (PauliGroundStateWeak.full_weak_equation C e F χ A₂ v₂ c hc p h₂) hn

end PfHk.PauliHohenbergKohn

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
