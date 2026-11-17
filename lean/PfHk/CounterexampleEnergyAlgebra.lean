import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Real-number accounting for the zero-coupling energy decomposition.
These lemmas keep scalar algebra independent of the physical operator
representatives and their typeclass instances. -/

namespace PfHk.CounterexampleEnergyAlgebra

set_option autoImplicit false
set_option Elab.async false

/-- Regroup kinetic, radiation, Coulomb and magnetic energies. -/
theorem regroup (k r Z c t m : ℝ) :
    k + r + (-Z * c) + t * m = (k - Z * c + t * m) + r := by
  ring

/-- The same accounting when the scalar and vector pairings are grouped. -/
theorem regroup_pairing (k r Z c t m : ℝ) :
    k + r + (-Z * c + t * m) = (k - Z * c + t * m) + r := by
  ring

/-- Adding nonnegative radiation preserves an electronic lower bound. -/
theorem lower_bound {lower electronic radiation physical : ℝ}
    (he : lower ≤ electronic) (hr : 0 ≤ radiation)
    (hp : physical = electronic + radiation) : lower ≤ physical := by
  linarith only [he, hr, hp]

/-- Equality at the total lower bound fixes the electronic energy and
forces the nonnegative radiation contribution to vanish. -/
theorem equality_parts {lower electronic radiation physical : ℝ}
    (he : lower ≤ electronic) (hr : 0 ≤ radiation)
    (hp : physical = electronic + radiation) (hu : physical ≤ lower) :
    electronic = lower ∧ radiation = 0 := by
  constructor <;> linarith only [he, hr, hp, hu]

/-- A unit-norm state removes the norm factor in the hydrogenic level. -/
theorem normalized_level (Z n : ℝ) (hn : n = 1) :
    -(Z ^ 2 / 2) * n ^ 2 = -(Z ^ 2 / 2) := by
  rw [hn, one_pow, mul_one]

theorem normalized_lower_bound {Z n electronic : ℝ} (hn : n = 1)
    (he : -(Z ^ 2 / 2) * n ^ 2 ≤ electronic) : -(Z ^ 2 / 2) ≤ electronic := by
  simpa only [hn, one_pow, mul_one] using he

/-- A zero square of a real norm yields zero without exposing the norm's
underlying space to arithmetic normalization. -/
theorem zero_of_square_zero {n : ℝ} (h : n ^ 2 = 0) : n = 0 :=
  sq_eq_zero_iff.mp h

end PfHk.CounterexampleEnergyAlgebra
