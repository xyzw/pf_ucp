import GptLean.PhysicalFockCreationWords

/-!
Bounded number-truncated creation and annihilation on the same Fock model.
These operators are finite sums of the actual adjacent-sector operators.
Their actions on inserted sectors are proved, so identities on finite
creation words can later be extended by ordinary Hilbert-space continuity.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

def creationBlock (n : ℕ) (f : Lp ℂ 2 μ) : Fock μ →L[ℂ] Fock μ :=
  (lp.singleContinuousLinearMap ℂ (Sector μ) 2 (n + 1)).comp
    ((creationSector μ n f).comp (lp.evalCLM ℂ (Sector μ) 2 n))

def annihilationBlock (n : ℕ) (f : Lp ℂ 2 μ) : Fock μ →L[ℂ] Fock μ :=
  (lp.singleContinuousLinearMap ℂ (Sector μ) 2 n).comp
    ((annihilationSector μ n f).comp (lp.evalCLM ℂ (Sector μ) 2 (n + 1)))

@[simp] theorem creationBlock_single (n : ℕ) (f : Lp ℂ 2 μ) (u : Sector μ n) :
    creationBlock μ n f (lp.single 2 n u) = lp.single 2 (n + 1) (creationSector μ n f u) := by
  change lp.single 2 (n + 1) (creationSector μ n f ((lp.single 2 n u) n)) = _
  rw [lp.single_apply_self]

@[simp] theorem annihilationBlock_single (n : ℕ) (f : Lp ℂ 2 μ) (u : Sector μ (n + 1)) :
    annihilationBlock μ n f (lp.single 2 (n + 1) u) = lp.single 2 n (annihilationSector μ n f u) := by
  change lp.single 2 n (annihilationSector μ n f ((lp.single 2 (n + 1) u) (n + 1))) = _
  rw [lp.single_apply_self]

theorem creationBlock_single_ne (n m : ℕ) (hnm : n ≠ m) (f : Lp ℂ 2 μ) (u : Sector μ m) :
    creationBlock μ n f (lp.single 2 m u) = 0 := by
  change lp.single 2 (n + 1) (creationSector μ n f ((lp.single 2 m u) n)) = 0
  rw [lp.single_apply_ne _ _ _ hnm, map_zero, lp.single_zero]

theorem annihilationBlock_single_ne (n m : ℕ) (hnm : n + 1 ≠ m)
    (f : Lp ℂ 2 μ) (u : Sector μ m) :
    annihilationBlock μ n f (lp.single 2 m u) = 0 := by
  change lp.single 2 n (annihilationSector μ n f ((lp.single 2 m u) (n + 1))) = 0
  rw [lp.single_apply_ne _ _ _ hnm, map_zero, lp.single_zero]

/-- Creation on input sectors at most `M`. -/
def creationFinite (M : ℕ) (f : Lp ℂ 2 μ) : Fock μ →L[ℂ] Fock μ :=
  ∑ n ∈ Finset.range (M + 1), creationBlock μ n f

/-- Annihilation on input sectors at most `M`, with zero on the vacuum. -/
def annihilationFinite (M : ℕ) (f : Lp ℂ 2 μ) : Fock μ →L[ℂ] Fock μ :=
  ∑ n ∈ Finset.range M, annihilationBlock μ n f

theorem creationFinite_single (M n : ℕ) (hn : n ≤ M) (f : Lp ℂ 2 μ) (u : Sector μ n) :
    creationFinite μ M f (lp.single 2 n u) = lp.single 2 (n + 1) (creationSector μ n f u) := by
  classical
  simp only [creationFinite, sum_apply]
  rw [Finset.sum_eq_single n]
  · exact creationBlock_single μ n f u
  · intro m _ hmn
    exact creationBlock_single_ne μ m n hmn f u
  · intro hn'
    exact False.elim (hn' (Finset.mem_range.mpr (by omega)))

theorem annihilationFinite_single (M n : ℕ) (hn : n < M) (f : Lp ℂ 2 μ)
    (u : Sector μ (n + 1)) :
    annihilationFinite μ M f (lp.single 2 (n + 1) u) =
      lp.single 2 n (annihilationSector μ n f u) := by
  classical
  simp only [annihilationFinite, sum_apply]
  rw [Finset.sum_eq_single n]
  · exact annihilationBlock_single μ n f u
  · intro m _ hmn
    exact annihilationBlock_single_ne μ m (n + 1) (by omega) f u
  · intro hn'
    exact False.elim (hn' (Finset.mem_range.mpr hn))

theorem annihilationFinite_vacuum (M : ℕ) (f : Lp ℂ 2 μ) :
    annihilationFinite μ M f (creationWord μ []) = 0 := by
  classical
  simp only [annihilationFinite, sum_apply, creationWord_nil]
  apply Finset.sum_eq_zero
  intro n _
  exact annihilationBlock_single_ne μ n 0 (by omega) f (vacuumSector μ)

theorem creationFinite_word (M : ℕ) (f : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ))
    (hw : w.length ≤ M) :
    creationFinite μ M f (creationWord μ w) = creationWord μ (f :: w) :=
  creationFinite_single μ M w.length hw f (creationWordSector μ w)

theorem photonSector_word (n : ℕ) (w : List (Lp ℂ 2 μ)) :
    photonSector μ n (creationWord μ w) = if n = w.length then creationWord μ w else 0 := by
  classical
  by_cases hn : n = w.length
  · subst n
    change lp.single 2 w.length ((lp.single 2 w.length (creationWordSector μ w)) w.length) = _
    rw [lp.single_apply_self, ite_eq_left rfl]
    rfl
  · change lp.single 2 n ((lp.single 2 w.length (creationWordSector μ w)) n) = _
    rw [lp.single_apply_ne _ _ _ hn, lp.single_zero, ite_eq_right hn]

end GptLean.PhysicalFock
