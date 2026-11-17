import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.SplitIfs

/-! Finite-sum reduction for a rotated vector field supported at one
electron index. These identities isolate the two curl coordinates. -/

noncomputable section
namespace PfHk.PauliClassicalCurlRotationAlgebra

open scoped BigOperators InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 30000

variable {N : ℕ}

def singleRotation {H : Type*} [Zero H] [Neg H]
    (n : Fin N) (a b : Fin 3) (u : Fin 3 → H) (i : Fin N × Fin 3) : H :=
  if i.1 = n then (if i.2 = a then u b else if i.2 = b then -u a else 0) else 0

theorem singleRotation_eq {H : Type*} [AddGroup H]
    (n : Fin N) (a b : Fin 3) (hab : a ≠ b) (u : Fin 3 → H)
    (i : Fin N × Fin 3) :
    singleRotation n a b u i =
      (if i = (n, a) then u b else 0) - (if i = (n, b) then u a else 0) := by
  rcases i with ⟨m, k⟩
  by_cases hmn : m = n
  · subst m
    by_cases hka : k = a
    · subst k
      simp [singleRotation, hab]
    · by_cases hkb : k = b
      · subst k
        simp [singleRotation, Ne.symm hab]
      · simp [singleRotation, hka, hkb]
  · simp [singleRotation, hmn]

theorem sum_single {V : Type*} [AddCommMonoid V] (n : Fin N) (z : V) :
    (∑ m : Fin N, if m = n then z else 0) = z := by
  simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_singleRotation_right (n : Fin N) (a b : Fin 3) (hab : a ≠ b)
    (d : Fin N × Fin 3 → H) (u : Fin 3 → H) :
    (∑ i, inner ℂ (d i) (singleRotation n a b u i)) =
      inner ℂ (d (n, a)) (u b) - inner ℂ (d (n, b)) (u a) := by
  have hi (i : Fin N × Fin 3) : inner ℂ (d i) (singleRotation n a b u i) =
      (if i = (n, a) then inner ℂ (d i) (u b) else 0) -
        (if i = (n, b) then inner ℂ (d i) (u a) else 0) := by
    rw [singleRotation_eq n a b hab u i, inner_sub_right]
    split_ifs <;> simp only [inner_zero_right]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_sub_distrib]
  simp

theorem inner_singleRotation_left (n : Fin N) (a b : Fin 3) (hab : a ≠ b)
    (d : Fin N × Fin 3 → H) (u : Fin 3 → H) :
    (∑ i, inner ℂ (singleRotation n a b u i) (d i)) =
      inner ℂ (u b) (d (n, a)) - inner ℂ (u a) (d (n, b)) := by
  have hi (i : Fin N × Fin 3) : inner ℂ (singleRotation n a b u i) (d i) =
      (if i = (n, a) then inner ℂ (u b) (d i) else 0) -
        (if i = (n, b) then inner ℂ (u a) (d i) else 0) := by
    rw [singleRotation_eq n a b hab u i, inner_sub_left]
    split_ifs <;> simp only [inner_zero_left]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_sub_distrib]
  simp

end PfHk.PauliClassicalCurlRotationAlgebra
