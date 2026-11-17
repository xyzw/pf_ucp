import PfHk.PauliCoefficientBounds

/-! Lower bounds and recovery of all free graph energies for the physical
Pauli form with global L3+L-infinity vector potentials and
L^(3/2)+L-infinity scalar potentials. All absorption constants are
constructed from the coefficient classes. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PauliPhysicalFormBounds

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.PhysicalPairDuality PfHk.PhysicalLocalEnergy
open PfHk.PhysicalCommonFormDomain PfHk.PauliGroundState PfHk.PauliFormBounds

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

variable {N : ℕ}

attribute [local irreducible] referenceSubspace inclusion ordinary radiation
  PhysicalPFReference.field rawCovariant rawContraction externalCovariant roughMultiply rawForm rawEnergy

/-- A choice of constants whose multiplier properties are derived below
from the actual global coefficients. -/
structure SmallConstants (N : ℕ) (A : VectorPotential) (v : ScalarPotential) (c e M : ℝ) where
  vectorRate : ℝ
  vectorRate_pos : 0 < vectorRate
  vectorMass : ℝ
  vectorMass_nonneg : 0 ≤ vectorMass
  vector_bound : ∀ q : Fin N × Fin 3, ScalarMultiplierBound (vector A q) vectorRate vectorMass
  vector_small : 9 * (Fintype.card (Fin N × Fin 3) : ℝ) * vectorRate ≤ 1 / 2
  scalarRate : ℝ
  scalarRate_pos : 0 < scalarRate
  scalarMass : ℝ
  scalarMass_nonneg : 0 ≤ scalarMass
  scalar_bound : ScalarMultiplierBound (negative (N := N) v c) scalarRate scalarMass
  scalar_small : scalarRate * recoveryFactor N e M ≤ 1 / 4

theorem smallConstants_nonempty (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (e M : ℝ) : Nonempty (SmallConstants N A v c e M) := by
  let d : ℝ := Fintype.card (Fin N × Fin 3)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  let ε : ℝ := 1 / (18 * (d + 1))
  have hε : 0 < ε := one_div_pos.mpr (by positivity)
  obtain ⟨C_A, hC_A, hA⟩ := PauliCoefficientBounds.vector_small_form (N := N) A hε
  have hs : 9 * d * ε ≤ 1 / 2 := by
    have heq : (18 * (d + 1)) * ε = 1 := mul_one_div_cancel (by positivity)
    have hp : 0 ≤ ε := hε.le
    nlinarith only [heq, hp]
  have hr : 0 ≤ recoveryFactor N e M := by
    unfold recoveryFactor
    positivity
  let δ : ℝ := 1 / (4 * (recoveryFactor N e M + 1))
  have hδ : 0 < δ := one_div_pos.mpr (by positivity)
  obtain ⟨C₀, hC₀, hv⟩ := PauliCoefficientBounds.negative_small_form (N := N) v c hc hδ
  have hvs : δ * recoveryFactor N e M ≤ 1 / 4 := by
    have heq : (4 * (recoveryFactor N e M + 1)) * δ = 1 := mul_one_div_cancel (by positivity)
    have hp : 0 ≤ δ := hδ.le
    nlinarith only [heq, hp]
  exact ⟨⟨ε, hε, C_A, hC_A, hA, hs, δ, hδ, C₀, hC₀, hv, hvs⟩⟩

def constants (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (e M : ℝ) : SmallConstants N A v c e M :=
  Classical.choice (smallConstants_nonempty A v c hc e M)

def lowerMass (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (e M : ℝ) : ℝ :=
  let k := constants (N := N) A v c hc e M
  k.scalarMass + k.scalarRate * massFactor N e M k.vectorMass

theorem lowerMass_nonneg (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (e M : ℝ) : 0 ≤ lowerMass (N := N) A v c hc e M := by
  let k := constants (N := N) A v c hc e M
  have hA := k.vectorMass_nonneg
  have hmass : 0 ≤ massFactor N e M k.vectorMass := by
    unfold massFactor
    positivity
  exact add_nonneg k.scalarMass_nonneg (mul_nonneg k.scalarRate_pos.le hmass)

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

theorem form_lower_bound (u : Ref N) :
    (pauliEnergy C κ hκ M hκbound e (vector A) (positive v c) (negative v c) u
        (PauliCoefficientBounds.domain A v c hc u) + radiationEnergy (N := N) u) / 4 -
      lowerMass (N := N) A v c hc e M * normSquared (N := N) u ≤
      rawEnergy C κ hκ M hκbound e (vector A) (positive v c) (negative v c) u
        (PauliCoefficientBounds.domain A v c hc u) := by
  let k := constants (N := N) A v c hc e M
  exact PauliFormBounds.form_lower_bound C κ hκ M hκbound e
    (vector A) (positive v c) (negative v c)
    k.vectorRate k.vectorMass k.vectorRate_pos.le k.vector_bound k.vector_small
    k.scalarRate k.scalarMass k.scalarRate_pos.le k.scalar_bound k.scalar_small
    u (PauliCoefficientBounds.domain A v c hc u)

theorem semibounded (u : Ref N) :
    -(lowerMass (N := N) A v c hc e M) * normSquared (N := N) u ≤
      rawEnergy C κ hκ M hκbound e (vector A) (positive v c) (negative v c) u
        (PauliCoefficientBounds.domain A v c hc u) := by
  have h := form_lower_bound C κ hκ M hκbound e A v c hc u
  have hp := pauliEnergy_nonneg C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
    u (PauliCoefficientBounds.domain A v c hc u)
  have hr := radiationEnergy_nonneg (N := N) u
  linarith only [h, hp, hr]

def fullMass (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (e M : ℝ) : ℝ :=
  4 * (recoveryFactor N e M + 1) * lowerMass (N := N) A v c hc e M +
    massFactor N e M (constants (N := N) A v c hc e M).vectorMass

theorem fullMass_nonneg : 0 ≤ fullMass (N := N) A v c hc e M := by
  have hR : 0 ≤ recoveryFactor N e M := by
    unfold recoveryFactor
    positivity
  have hL := lowerMass_nonneg (N := N) A v c hc e M
  have hA := (constants (N := N) A v c hc e M).vectorMass_nonneg
  unfold fullMass massFactor
  positivity

theorem full_energy_bound (u : Ref N) :
    ordinaryEnergy (N := N) u +
      pauliEnergy C κ hκ M hκbound e (vector A) (positive v c) (negative v c) u
        (PauliCoefficientBounds.domain A v c hc u) + radiationEnergy (N := N) u ≤
      4 * (recoveryFactor N e M + 1) *
        rawEnergy C κ hκ M hκbound e (vector A) (positive v c) (negative v c) u
          (PauliCoefficientBounds.domain A v c hc u) +
        fullMass (N := N) A v c hc e M * normSquared (N := N) u := by
  let k := constants (N := N) A v c hc e M
  exact PauliFormBounds.full_energy_bound C κ hκ M hκbound e
    (vector A) (positive v c) (negative v c)
    k.vectorRate k.vectorMass k.vectorRate_pos.le k.vector_bound k.vector_small
    k.scalarRate k.scalarMass k.scalarRate_pos.le k.scalar_bound k.scalar_small
    u (PauliCoefficientBounds.domain A v c hc u)

end PfHk.PauliPhysicalFormBounds
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
