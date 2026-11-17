import PfHk.PauliGroundState
import PfHk.PhysicalScalarFormDifference

/-! Subtracting the actual Pauli forms with the same external vector
potential cancels the coupled kinetic term. Only the physical scalar
multiplier remains, summed over the finite spin components. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliScalarFormDifference

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.PauliGroundState PfHk.PauliSpin

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] referenceSubspace inclusion covariant radiation
  roughMultiply externalCovariant

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

theorem contraction_congr (hA : A₁.val =ᵐ[volume] A₂.val)
    (u : Ref N) (n : Fin N) :
    rawContraction C κ hκ M hb e (vector A₁) (positive v₁ c) (negative v₁ c)
      u (D₁ u) n =
    rawContraction C κ hκ M hb e (vector A₂) (positive v₂ c) (negative v₂ c)
      u (D₂ u) n := by
  unfold rawContraction
  apply congrArg (PauliCurrentAlgebra.contraction n)
  funext a s
  exact PhysicalScalarFormDifference.externalCovariant_congr
    C κ hκ M hb e A₁ A₂ v₁ v₂ c hc hA (u s) (n, a)

private theorem form_accounting {S : Type*} [Fintype S]
    (k₁ k₂ r : ℂ) (p₁ m₁ p₂ m₂ : S → ℂ) (hk : k₁ = k₂) :
    (k₁ + r + ∑ s, p₁ s - ∑ s, m₁ s).re -
      (k₂ + r + ∑ s, p₂ s - ∑ s, m₂ s).re =
        ∑ s, ((p₁ s).re - (m₁ s).re - ((p₂ s).re - (m₂ s).re)) := by
  rw [hk]
  simp only [Complex.add_re, Complex.sub_re, Complex.re_sum, Finset.sum_sub_distrib]
  ring

theorem difference (hA : A₁.val =ᵐ[volume] A₂.val) (z u : Ref N) :
    (rawForm C κ hκ M hb e (vector A₁) (positive v₁ c) (negative v₁ c)
      z u (D₁ z) (D₁ u)).re -
    (rawForm C κ hκ M hb e (vector A₂) (positive v₂ c) (negative v₂ c)
      z u (D₂ z) (D₂ u)).re =
      ∑ s, ∫ X, PhysicalScalarFormDifference.scalarDifference (N := N) v₁ v₂ X *
        (inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s) X)
          (inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)).re := by
  have hk :
      ((1 / 2 : ℂ) * ∑ n, ∑ s,
        inner ℂ (rawContraction C κ hκ M hb e (vector A₁) (positive v₁ c)
          (negative v₁ c) z (D₁ z) n s)
          (rawContraction C κ hκ M hb e (vector A₁) (positive v₁ c)
            (negative v₁ c) u (D₁ u) n s)) =
      (1 / 2 : ℂ) * ∑ n, ∑ s,
        inner ℂ (rawContraction C κ hκ M hb e (vector A₂) (positive v₂ c)
          (negative v₂ c) z (D₂ z) n s)
          (rawContraction C κ hκ M hb e (vector A₂) (positive v₂ c)
            (negative v₂ c) u (D₂ u) n s) := by
    simp only [contraction_congr C κ hκ M hb e A₁ A₂ v₁ v₂ c hc hA]
  unfold rawForm
  refine (form_accounting _ _ _ _ _ _ _ hk).trans ?_
  apply Finset.sum_congr rfl
  intro s _
  have h₁ := PhysicalScalarFormDifference.scalar_pair_re v₁ c (z s) (u s)
    ((D₁ z s).positive) ((D₁ u s).positive) ((D₁ z s).negative) ((D₁ u s).negative)
  have h₂ := PhysicalScalarFormDifference.scalar_pair_re v₂ c (z s) (u s)
    ((D₂ z s).positive) ((D₂ u s).positive) ((D₂ z s).negative) ((D₂ u s).negative)
  have hi₁ := PhysicalScalarFormDifference.scalar_pair_integrable v₁ c (z s) (u s)
    ((D₁ z s).positive) ((D₁ u s).positive) ((D₁ z s).negative) ((D₁ u s).negative)
  have hi₂ := PhysicalScalarFormDifference.scalar_pair_integrable v₂ c (z s) (u s)
    ((D₂ z s).positive) ((D₂ u s).positive) ((D₂ z s).negative) ((D₂ u s).negative)
  refine (congrArg₂ (· - ·) h₁ h₂).trans ((integral_sub hi₁ hi₂).symm.trans ?_)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun X =>
    (sub_mul _ _ _).symm.trans (congrArg
      (fun t : ℝ => t * (inner ℂ
        (inclusion (Fin N × Fin 3) (fun _ => 0) (z s) X)
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)).re)
      (PhysicalScalarFormDifference.scalar_sub v₁ v₂ c X))

end PfHk.PauliScalarFormDifference

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
