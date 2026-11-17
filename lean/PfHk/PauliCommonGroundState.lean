import PfHk.PauliExternalEnergy

/-! Equality of the physical spinful density-current pairs supplies common
variational ground states for the two actual Pauli Hamiltonians. -/

noncomputable section
namespace PfHk.PauliGroundState

open GptLean GptLean.PhysicalFock GptLean.PhysicalPairDuality GptLean.PhysicalPolarization

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [local irreducible] energy data

private theorem intrinsic_cancel (r p q : ℝ) : (r + p) - (r + q) = p - q := by ring

private theorem minimum_equalities (a b c d t : ℝ)
    (h₁ : a - b = t) (h₂ : c - d = t) (ha : a ≤ c) (hb : d ≤ b) :
    a = c ∧ b = d := by
  constructor <;> linarith only [h₁, h₂, ha, hb]

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (F : Frame)
  (χ : ArticleCutoff) (hN : 0 < N)
  (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

include hN

theorem energy_difference (u : Ref N) :
    energy C e F χ A₁ v₁ c hc u - energy C e F χ A₂ v₂ c hc u =
      pairPotential (PhysicalDiamagneticPotential.shifted v₁ A₁) (data C e F χ u) -
        pairPotential (PhysicalDiamagneticPotential.shifted v₂ A₂) (data C e F χ u) := by
  exact (congrArg₂ (fun x y : ℝ => x - y)
    (PauliExternalEnergy.energy_decomposition C e F χ hN A₁ v₁ c hc u)
    (PauliExternalEnergy.energy_decomposition C e F χ hN A₂ v₂ c hc u)).trans
      (intrinsic_cancel _ _ _)

theorem common_ground_state (p₁ p₂ : State N)
    (h₁ : IsGroundState C e F χ A₁ v₁ c hc p₁)
    (h₂ : IsGroundState C e F χ A₂ v₂ c hc p₂)
    (hd : data C e F χ p₁.vector = data C e F χ p₂.vector) :
    IsGroundState C e F χ A₁ v₁ c hc p₂ ∧
      IsGroundState C e F χ A₂ v₂ c hc p₁ ∧
      energy C e F χ A₁ v₁ c hc p₁.vector - energy C e F χ A₂ v₂ c hc p₂.vector =
        pairPotential (PhysicalDiamagneticPotential.shifted v₁ A₁) (data C e F χ p₁.vector) -
          pairPotential (PhysicalDiamagneticPotential.shifted v₂ A₂) (data C e F χ p₁.vector) := by
  have hd₁ := energy_difference C e F χ hN A₁ A₂ v₁ v₂ c hc p₁.vector
  have hd₂ := (energy_difference C e F χ hN A₁ A₂ v₁ v₂ c hc p₂.vector).trans
    (congrArg (fun P : PhysicalPairSpace.Pair =>
      pairPotential (PhysicalDiamagneticPotential.shifted v₁ A₁) P -
        pairPotential (PhysicalDiamagneticPotential.shifted v₂ A₂) P) hd.symm)
  have he := minimum_equalities _ _ _ _ _ hd₁ hd₂ (h₁ p₂) (h₂ p₁)
  have he₁ := he.1
  have he₂ := he.2
  refine ⟨?_, ?_, ?_⟩
  · intro q
    exact he₁.symm.le.trans (h₁ q)
  · intro q
    exact he₂.le.trans (h₂ q)
  · exact (congrArg (fun r : ℝ => energy C e F χ A₁ v₁ c hc p₁.vector - r) he₂).symm.trans hd₁

end PfHk.PauliGroundState
