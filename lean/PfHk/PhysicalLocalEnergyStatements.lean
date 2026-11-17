import PfHk.PhysicalLocalEnergyBumps
import PfHk.PhysicalLocalEnergyCutoff
import PfHk.PhysicalUCPSmallForm

/-! Statement-level form of the spinless local kinetic energy estimates
`ucp-caccioppoli`. Part (i) bounds the covariant and radiation energies on
the inner ball and needs only the quarter form bound of the negative
scalar part. Part (ii) bounds the gradient of the localized norm for every
admissible cutoff. One constant serves every center, every radius at most
one and every cutoff with the given gradient constant. -/

noncomputable section

namespace PfHk.PhysicalLocalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply
  massOn externalCovariant externalEnergy normGradientEnergy roughMultiply

variable {I : Type} [Fintype I] [DecidableEq I]

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

/-- The covariant and radiation energies on the inner ball are controlled
by the localized ones. No ordinary derivative is involved. -/
theorem covariant_radiation_on_ball_le_localized (u : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    {x₀ : Position I} {r L : ℝ} (a : BallCutoff x₀ r L) :
    (∑ i, massOn (Metric.ball x₀ r)
        (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
      massOn (Metric.ball x₀ r) (radiation I V u) ≤
    (∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative
        (PhysicalPFScalarMultiplier.multiply V a.multiplier u) (hu.localize V a.multiplier) i‖ ^ 2) +
      ‖radiation I V (PhysicalPFScalarMultiplier.multiply V a.multiplier u)‖ ^ 2 := by
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    exact a.local_norm_bound i (-Complex.I) (inclusion I V u) _ _
      (externalCovariant_localize V C κ hκ M hbound e A positive negative u hu a.multiplier i)
  · exact a.local_multiplier_bound _ _ (PhysicalPFScalarMultiplier.radiation_multiply V a.multiplier u)

/-- Both parts of `ucp-caccioppoli` for one cutoff, with the explicit constant. -/
theorem kinetic_estimates {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hSob : ScalarMultiplierBound negative (1 / 4) C₀)
    {x₀ : Position I} {r L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (a : BallCutoff x₀ r L) :
    ((∑ i, massOn (Metric.ball x₀ r)
        (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
      massOn (Metric.ball x₀ r) (radiation I V u) ≤
      (8 * (|E| + |C₀|) + 4 * (Fintype.card I) * L ^ 2) / r ^ 2 *
        massOn (Metric.ball x₀ (2 * r)) (inclusion I V u)) ∧
    normGradientEnergy V (PhysicalPFScalarMultiplier.multiply V a.multiplier u) ≤
      (8 * (|E| + |C₀|) + 4 * (Fintype.card I) * L ^ 2) / r ^ 2 *
        massOn (Metric.ball x₀ (2 * r)) (inclusion I V u) := by
  have h := caccioppoli_localized V C κ hκ M hbound e A positive negative
    heigen C₀ hSob hr hr1 a
  have hg := normGradientEnergy_nonneg V (PhysicalPFScalarMultiplier.multiply V a.multiplier u)
  have hl := covariant_radiation_on_ball_le_localized V C κ hκ M hbound e A positive negative
    u hu a
  exact ⟨hl.trans ((le_add_of_nonneg_right hg).trans h),
    caccioppoli_normGradient V C κ hκ M hbound e A positive negative heigen C₀ hSob hr hr1 a⟩

/-- `ucp-caccioppoli` (i). The constant does not depend on the center or
the radius. The cutoff is constructed from the fixed smooth bump. -/
theorem exists_local_energy_constant {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hSob : ScalarMultiplierBound negative (1 / 4) C₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x₀ : Position I) (r : ℝ), 0 < r → r ≤ 1 →
      (∑ i, massOn (Metric.ball x₀ r)
          (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
        massOn (Metric.ball x₀ r) (radiation I V u) ≤
      K / r ^ 2 * massOn (Metric.ball x₀ (2 * r)) (inclusion I V u) :=
  ⟨8 * (|E| + |C₀|) + 4 * (Fintype.card I) * (ballCutoffConstant (I := I)) ^ 2, by positivity,
    fun x₀ r hr hr1 => (kinetic_estimates V C κ hκ M hbound e A positive negative
      heigen C₀ hSob hr hr1 (ballCutoff x₀ r hr)).1⟩

/-- `ucp-caccioppoli` (ii). The constant depends on the cutoff only
through its gradient constant `L`. -/
theorem exists_localized_gradient_constant {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hSob : ScalarMultiplierBound negative (1 / 4) C₀) (L : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x₀ : Position I) (r : ℝ), 0 < r → r ≤ 1 →
      ∀ a : BallCutoff x₀ r L,
      normGradientEnergy V (PhysicalPFScalarMultiplier.multiply V a.multiplier u) ≤
        K / r ^ 2 * massOn (Metric.ball x₀ (2 * r)) (inclusion I V u) :=
  ⟨8 * (|E| + |C₀|) + 4 * (Fintype.card I) * L ^ 2, by positivity,
    fun _ _ hr hr1 a => (kinetic_estimates V C κ hκ M hbound e A positive negative
      heigen C₀ hSob hr hr1 a).2⟩

end PfHk.PhysicalLocalEnergy

namespace PfHk.PhysicalUCPCoefficients

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.PhysicalLocalEnergy

set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply
  massOn externalCovariant externalEnergy normGradientEnergy roughMultiply

variable {N : ℕ} {U : Set (Configuration N)}
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ X ∂volume, ‖κ i X‖ ≤ M) (e : ℝ)

/-- `ucp-caccioppoli` (i) for the physical coefficient classes. The form
bound of the negative scalar part is derived from the global scalar class. -/
theorem Data.exists_local_energy_constant (a : Data N U) {E : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u}
    (heigen : IsExternalWeakEigenstate (fun _ => 0) C κ hκ M hbound e
      a.vector a.positive a.negative E u hu) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X₀ : Configuration N) (r : ℝ), 0 < r → r ≤ 1 →
      (∑ i, massOn (Metric.ball X₀ r)
          (externalCovariant (fun _ => 0) C κ hκ M hbound e
            a.vector a.positive a.negative u hu i)) +
        massOn (Metric.ball X₀ r) (radiation (Fin N × Fin 3) (fun _ => 0) u) ≤
      K / r ^ 2 * massOn (Metric.ball X₀ (2 * r))
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) := by
  have hq := a.negative_quarter_form
  rcases hq with ⟨C₀, _, hSob⟩
  exact PhysicalLocalEnergy.exists_local_energy_constant (fun _ => 0) C κ hκ M hbound e
    a.vector a.positive a.negative heigen C₀ hSob

/-- `ucp-caccioppoli` (ii) for the physical coefficient classes. -/
theorem Data.exists_localized_gradient_constant (a : Data N U) {E : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u}
    (heigen : IsExternalWeakEigenstate (fun _ => 0) C κ hκ M hbound e
      a.vector a.positive a.negative E u hu) (L : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X₀ : Configuration N) (r : ℝ), 0 < r → r ≤ 1 →
      ∀ η : BallCutoff X₀ r L,
      normGradientEnergy (fun _ => 0)
          (PhysicalPFScalarMultiplier.multiply (fun _ => 0) η.multiplier u) ≤
        K / r ^ 2 * massOn (Metric.ball X₀ (2 * r))
          (inclusion (Fin N × Fin 3) (fun _ => 0) u) := by
  have hq := a.negative_quarter_form
  rcases hq with ⟨C₀, _, hSob⟩
  exact PhysicalLocalEnergy.exists_localized_gradient_constant (fun _ => 0) C κ hκ M hbound e
    a.vector a.positive a.negative heigen C₀ hSob L

end PfHk.PhysicalUCPCoefficients
