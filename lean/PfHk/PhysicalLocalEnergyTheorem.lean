import PfHk.PhysicalLocalEnergyBumps
import PfHk.PhysicalLocalEnergyCutoff

/-! Uniform-constant statement of the physical local-energy theorem. -/
noncomputable section
namespace PfHk.PhysicalLocalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference

set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 40000
set_option Elab.async false

variable {I : Type} [Fintype I] [DecidableEq I]

def caccioppoliConstant (d : ℕ) (e M E C₀ C_A L : ℝ) : ℝ :=
  derivativeRecoveryFactor d e M * (8 * (|E| + |C₀|) + 4 * d * L ^ 2) +
    derivativeMassFactor d e M C_A

theorem caccioppoliConstant_nonneg (d : ℕ) (e M E C₀ C_A L : ℝ) :
    0 ≤ caccioppoliConstant d e M E C₀ C_A L := by
  exact add_nonneg
    (mul_nonneg (derivativeRecoveryFactor_nonneg d e M) (by positivity))
    (derivativeMassFactor_nonneg d e M C_A)

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply
  massOn externalCovariant externalEnergy normGradientEnergy roughMultiply

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

/-- The full physical local-energy estimate, with one constant for every
center and every radius at most one. The scalar cutoffs are constructed
in the proof from the fixed smooth bump. -/
theorem exists_caccioppoli_constant {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ C_A : ℝ) (hSob : ScalarMultiplierBound negative (1 / 4) C₀)
    (hA : ∀ i, ScalarMultiplierBound (A i) 1 C_A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x₀ : Position I) (r : ℝ), 0 < r → r ≤ 1 →
      (∑ i, massOn (Metric.ball x₀ r) (ordinary I V i u)) +
        (∑ i, massOn (Metric.ball x₀ r)
          (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
        massOn (Metric.ball x₀ r) (radiation I V u) ≤
      K / r ^ 2 * massOn (Metric.ball x₀ (2 * r)) (inclusion I V u) :=
  ⟨caccioppoliConstant (Fintype.card I) e M E C₀ C_A (ballCutoffConstant (I := I)),
    caccioppoliConstant_nonneg (Fintype.card I) e M E C₀ C_A (ballCutoffConstant (I := I)),
    fun x₀ r hr hr1 => caccioppoli (I := I) V C κ hκ M hbound e A positive negative
      heigen C₀ C_A hSob hA hr hr1 (ballCutoff x₀ r hr)⟩

end PfHk.PhysicalLocalEnergy
