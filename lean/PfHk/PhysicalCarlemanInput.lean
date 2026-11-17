import PfHk.PhysicalCutoffCommutator
import PfHk.UniqueContinuation

/-! The exact operator Carleman input needed by the continuation transfer.
This module does not assert that the physical coefficients satisfy it. Its
inequality is stated for every actual form-realized operator pair, and uses
nonnegative integrals so singular integrability is never implicit. -/

noncomputable section
namespace PfHk.PhysicalCarlemanInput

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier
open PfHk.PhysicalLocalEnergy PfHk.PhysicalCutoffCommutator
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFScalarMultiplier.multiply
  DifferentiableMultiplier.multiplier PfHk.PhysicalCutoffCommutator.commutator

private theorem cancel_equal {H : Type*} [AddCommGroup H] [Module ℂ H]
    (E : ℂ) (v w z : H) (h : v = w) : E • w + z - E • v = z := by
  rw [h]
  abel

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The essential support is contained in a compact annulus strictly inside
the stated ball. This is a geometric support condition on the actual field. -/
def AnnularSupport (ψ : WaveSpace I) (x₀ : Position I) (R : ℝ) : Prop :=
  ∃ ρ R' : ℝ, 0 < ρ ∧ ρ < R' ∧ R' < R ∧
    ∀ᵐ x ∂volume, (dist x x₀ < ρ ∨ R' < dist x x₀) → ψ x = 0

def sourceIntegrand (x₀ : Position I) (α τ : ℝ) (f : WaveSpace I) (x : Position I) : ℝ :=
  Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist x x₀))) *
    dist x x₀ ^ 2 * ‖f x‖ ^ 2

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

/-- A physical operator Carleman estimate, explicitly kept as the input to
the continuation argument until the radial-gauge proof discharges it. -/
def OperatorCarlemanAt (E : ℝ) (x₀ : Position I) (R α τ₀ K : ℝ) : Prop :=
  ∀ (u : Reference I V) (hu : ExternalDomain V A positive negative u) (f : WaveSpace I),
    IsOperatorPair V C κ hκ M hbound e A positive negative u hu f →
    AnnularSupport (inclusion I V u) x₀ R →
    ∀ τ : ℝ, τ₀ ≤ τ →
      (∫⁻ x in Metric.ball x₀ R,
        ENNReal.ofReal (UniqueContinuation.radialMassIntegrand (fun x => dist x x₀)
          (inclusion I V u) α τ x)) ≤
      ENNReal.ofReal K * (∫⁻ x in Metric.ball x₀ R,
        ENNReal.ofReal (sourceIntegrand x₀ α τ (f - (E : ℂ) • inclusion I V u) x))

/-- The actual localized weak eigenvector has the precise commutator source
required in the cutoff Carleman estimate. -/
theorem localized_eigenstate_estimate {E R α τ₀ K : ℝ} {x₀ : Position I}
    (hCarleman : OperatorCarlemanAt V C κ hκ M hbound e A positive negative E x₀ R α τ₀ K)
    (a : TwiceDifferentiableMultiplier I) {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (hsupp : AnnularSupport
      (inclusion I V (PhysicalPFScalarMultiplier.multiply V a.scalar u)) x₀ R)
    {τ : ℝ} (hτ : τ₀ ≤ τ) :
    (∫⁻ x in Metric.ball x₀ R,
      ENNReal.ofReal (UniqueContinuation.radialMassIntegrand (fun x => dist x x₀)
        (inclusion I V (PhysicalPFScalarMultiplier.multiply V a.scalar u)) α τ x)) ≤
      ENNReal.ofReal K * (∫⁻ x in Metric.ball x₀ R,
        ENNReal.ofReal (sourceIntegrand x₀ α τ
          (commutator V C κ hκ M hbound e A positive negative a u hu) x)) := by
  have h := hCarleman _ _ _
    (eigenstate_operatorPair_localize V C κ hκ M hbound e A positive negative a heigen) hsupp τ hτ
  have heq : (E : ℂ) • a.scalar.multiplier (H := PhotonFock) (inclusion I V u) +
      commutator V C κ hκ M hbound e A positive negative a u hu -
      (E : ℂ) • inclusion I V (PhysicalPFScalarMultiplier.multiply V a.scalar u) =
      commutator V C κ hκ M hbound e A positive negative a u hu :=
    cancel_equal (E : ℂ)
      (inclusion I V (PhysicalPFScalarMultiplier.multiply V a.scalar u))
      (a.scalar.multiplier (H := PhotonFock) (inclusion I V u))
      (commutator V C κ hκ M hbound e A positive negative a u hu)
      (PhysicalPFScalarMultiplier.value_multiply V a.scalar u)
  exact h.trans_eq (congrArg (fun z : WaveSpace I => ENNReal.ofReal K *
    (∫⁻ x in Metric.ball x₀ R, ENNReal.ofReal (sourceIntegrand x₀ α τ z x))) heq)

/-- Radius and constants are uniform for nearby centers. Every smaller
radius is included, as required for the relative-closedness propagation step. -/
def UniformLocalOperatorCarleman (E α : ℝ) (U : Set (Position I)) : Prop :=
  ∀ x₀ ∈ U, ∃ R₀ τ₀ K : ℝ, 0 < R₀ ∧ R₀ ≤ Real.exp (-2) ∧ 1 ≤ τ₀ ∧ 0 ≤ K ∧
    Metric.ball x₀ (4 * R₀) ⊆ U ∧ ∀ y ∈ Metric.ball x₀ R₀, ∀ R : ℝ, 0 < R → R ≤ R₀ →
      OperatorCarlemanAt V C κ hκ M hbound e A positive negative E y R α τ₀ K

end PfHk.PhysicalCarlemanInput
