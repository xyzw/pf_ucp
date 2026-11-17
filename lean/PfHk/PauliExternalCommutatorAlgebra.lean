import PfHk.PhysicalCutoffCommutatorCore
import Mathlib.Tactic.Ring

/-! Adding a real external vector potential to a weak covariant
commutator. The quadratic scalar terms cancel on the actual L2 domain,
without requiring a product of two coefficients to be an L2 multiplier. -/

noncomputable section
namespace PfHk.PauliExternalCommutatorAlgebra

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCutoffCommutator
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

theorem scalar_pair_commute {X H : Type*} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b : X → ℝ) (z u az bz au bu : Lp H 2 ν)
    (haz : az =ᵐ[ν] fun x => a x • z x)
    (hbz : bz =ᵐ[ν] fun x => b x • z x)
    (hau : au =ᵐ[ν] fun x => a x • u x)
    (hbu : bu =ᵐ[ν] fun x => b x • u x) :
    inner ℂ az bu = inner ℂ bz au := by
  apply l2_inner_eq_of_ae
  filter_upwards [haz, hbz, hau, hbu] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  simp only [inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul]
  exact congrArg (fun c : ℝ => c • inner ℂ (z x) (u x)) (mul_comm (b x) (a x))

/-- The only mixed term needed is the antisymmetric weak curl pairing.
No second derivative or product of two unbounded operators appears. -/
theorem add_scalar_commutator {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (diZ djZ diU djU aiZ ajZ aiU ajU : H) (quantumTerm classicalTerm : ℂ)
    (hq : inner ℂ diZ djU - inner ℂ djZ diU = quantumTerm)
    (hc : (inner ℂ diZ ajU - inner ℂ ajZ diU) -
      (inner ℂ djZ aiU - inner ℂ aiZ djU) = classicalTerm)
    (ha : inner ℂ aiZ ajU = inner ℂ ajZ aiU) :
    inner ℂ (diZ + aiZ) (djU + ajU) -
      inner ℂ (djZ + ajZ) (diU + aiU) = quantumTerm + classicalTerm := by
  rw [← hq, ← hc]
  simp only [inner_add_left, inner_add_right]
  rw [ha]
  ring

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

attribute [local irreducible] roughMultiply

variable {I : Type} [Fintype I] [DecidableEq I]

theorem rough_pair_commute (a b : Position I → ℝ) (z u : WaveSpace I)
    (haz : HasMultiplier a z) (hbz : HasMultiplier b z)
    (hau : HasMultiplier a u) (hbu : HasMultiplier b u) :
    inner ℂ (E := WaveSpace I) (roughMultiply a z haz) (roughMultiply b u hbu) =
      inner ℂ (E := WaveSpace I) (roughMultiply b z hbz) (roughMultiply a u hau) :=
  scalar_pair_commute (X := Position I) (H := PhotonFock) (ν := volume)
    a b z u (roughMultiply a z haz) (roughMultiply b z hbz)
    (roughMultiply a u hau) (roughMultiply b u hbu)
    (roughMultiply_ae a z haz) (roughMultiply_ae b z hbz)
    (roughMultiply_ae a u hau) (roughMultiply_ae b u hbu)

end PfHk.PauliExternalCommutatorAlgebra

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
