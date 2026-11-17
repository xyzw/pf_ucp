import PfHk.PauliCurrentCorrection

/-! Two-component identities for one electron, with arbitrary complex
Hilbert-space coefficients. -/

noncomputable section
namespace PfHk.SpinfulCounterexampleState
open PfHk.PauliSpin PfHk.PauliCurrentCorrection
open scoped InnerProductSpace
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000

def up : SpinIndex 1 := fun _ => 0
def down : SpinIndex 1 := fun _ => 1

theorem spin_cases (s : SpinIndex 1) : s = up ∨ s = down := by
  have h : s 0 = 0 ∨ s 0 = 1 := by omega
  rcases h with h | h
  · left
    funext n
    simpa only [Subsingleton.elim n 0, up] using h
  · right
    funext n
    simpa only [Subsingleton.elim n 0, down] using h

theorem sum_spin {M : Type*} [AddCommMonoid M] (f : SpinIndex 1 → M) :
    (∑ s, f s) = f up + f down := by
  classical
  have he : (Finset.univ : Finset (SpinIndex 1)) = {up, down} := by decide
  rw [he, Finset.sum_pair (by decide : up ≠ down)]

def downFamily {H : Type*} [Zero H] (u : H) : SpinIndex 1 → H :=
  fun s => if s 0 = 1 then u else 0

@[simp] theorem downFamily_up {H : Type*} [Zero H] (u : H) : downFamily u up = 0 := by
  simp [downFamily, up]
@[simp] theorem downFamily_down {H : Type*} [Zero H] (u : H) : downFamily u down = u := by
  simp [downFamily, down]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem spinPair_two (u v : SpinIndex 1 → H) :
    spinPair (0 : Fin 1) u v 2 = inner ℂ (u up) (v up) - inner ℂ (u down) (v down) := by
  simp only [spinPair, sum_spin, sigmaFamily_two, sign, up, down]
  norm_num [sub_eq_add_neg]

theorem spinPair_two_self_re (u : SpinIndex 1 → H) :
    (spinPair (0 : Fin 1) u u 2).re = ‖u up‖ ^ 2 - ‖u down‖ ^ 2 := by
  rw [spinPair_two, Complex.sub_re]
  congr 1 <;> exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

theorem spinPair_down (u v : H) (k : Fin 3) :
    spinPair (0 : Fin 1) (downFamily u) (downFamily v) k =
      if k = 2 then -inner ℂ u v else 0 := by
  fin_cases k <;> simp [spinPair, sum_spin, sigmaFamily, downFamily, PauliSpin.flip, sign, up, down]

end PfHk.SpinfulCounterexampleState
