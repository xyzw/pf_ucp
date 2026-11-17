import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Finite Hilbert pairing algebra for the actual source realization. -/
noncomputable section
namespace PfHk.PauliMagneticOperatorRealization
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

variable {S H : Type*} [Fintype S] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem assembled_source_pairing (P O B Q : ℂ) (z g a b q : S → H)
    (hP : P = O + B + Q)
    (hO : O = ∑ s, inner ℂ (z s) (g s + a s))
    (hB : B = ∑ s, inner ℂ (z s) (b s))
    (hQ : Q = ∑ s, inner ℂ (z s) (q s)) :
    P = ∑ s, inner ℂ (z s) (g s + (a s + b s + q s)) := by
  rw [hP, hO, hB, hQ]
  simp only [inner_add_right, Finset.sum_add_distrib]
  ring

end PfHk.PauliMagneticOperatorRealization
