import GptLean.PhysicalFockFiniteOperators
import GptLean.PhysicalFockMixedCCR

/-!
Finite-word contraction for the actual bounded sector operators.

The mixed CCR computes annihilation of a creation word as the sum over
deleting one kernel, with its actual one-photon inner-product coefficient.
This finite algebra is used for the channel intertwining identities.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

def wordContractionTerms (f : Lp ℂ 2 μ) : List (Lp ℂ 2 μ) →
    List (ℂ × List (Lp ℂ 2 μ))
  | [] => []
  | g :: w => (⟪f, g⟫_ℂ, w) ::
      (wordContractionTerms f w).map (fun p => (p.1, g :: p.2))

omit [SigmaFinite μ] in
theorem wordContractionTerms_length (f : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ)) :
    ∀ p ∈ wordContractionTerms μ f w, p.2.length + 1 = w.length := by
  induction w with
  | nil => simp [wordContractionTerms]
  | cons g w ih =>
    intro p hp
    simp only [wordContractionTerms, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · rfl
    · simpa only [List.length_cons] using congrArg (· + 1) (ih q hq)

def wordContraction (f : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ)) : Fock μ :=
  ((wordContractionTerms μ f w).map fun p => p.1 • creationWord μ p.2).sum

@[simp] theorem wordContraction_nil (f : Lp ℂ 2 μ) : wordContraction μ f [] = 0 := rfl

theorem wordContraction_cons (f g : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ)) :
    wordContraction μ f (g :: w) = ⟪f, g⟫_ℂ • creationWord μ w +
      creationFinite μ w.length g (wordContraction μ f w) := by
  simp only [wordContraction, wordContractionTerms, List.map_cons, List.sum_cons,
    List.map_map, map_list_sum]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply, map_smul]
  rw [creationFinite_word μ w.length g p.2 (by
    have h := wordContractionTerms_length μ f w p hp
    omega)]

variable (C : CanonicalSectorCCR μ)
include C

theorem annihilationFinite_word_cons (M : ℕ) (f g : Lp ℂ 2 μ)
    (w : List (Lp ℂ 2 μ)) (hw : w.length + 1 ≤ M) :
    annihilationFinite μ M f (creationWord μ (g :: w)) =
      ⟪f, g⟫_ℂ • creationWord μ w +
        creationFinite μ w.length g (annihilationFinite μ M f (creationWord μ w)) := by
  cases w with
  | nil =>
    rw [annihilationFinite_vacuum, map_zero, add_zero]
    change annihilationFinite μ M f
      (lp.single 2 1 (creationWordSector μ [g])) = _
    rw [annihilationFinite_single μ M 0 (by simp only [List.length_nil] at hw; omega) f,
      annihilation_creationWord_singleton μ C]
    exact (lp.singleContinuousLinearMap ℂ (Sector μ) 2 0).map_smul ⟪f, g⟫_ℂ _
  | cons h w =>
    have hlen : w.length < M := by simp only [List.length_cons] at hw; omega
    have hlen' : w.length + 1 < M := by simp only [List.length_cons] at hw; omega
    change annihilationFinite μ M f
      (lp.single 2 (w.length + 1 + 1) (creationWordSector μ (g :: h :: w))) = _
    rw [annihilationFinite_single μ M (w.length + 1) hlen' f,
      annihilation_creationWord_cons_cons μ C]
    change lp.single 2 (w.length + 1)
      (creationSector μ w.length g (annihilationSector μ w.length f (creationWordSector μ (h :: w))) +
        ⟪f, g⟫_ℂ • creationWordSector μ (h :: w)) =
      ⟪f, g⟫_ℂ • lp.single 2 (w.length + 1) (creationWordSector μ (h :: w)) +
        creationFinite μ (w.length + 1) g (annihilationFinite μ M f
          (lp.single 2 (w.length + 1) (creationWordSector μ (h :: w))))
    rw [annihilationFinite_single μ M w.length hlen f,
      creationFinite_single μ (w.length + 1) w.length (Nat.le_succ _) g]
    simp only [lp.single_add, lp.single_smul]
    exact add_comm _ _

/-- The actual bounded annihilator equals the finite kernel-deletion polynomial. -/
theorem annihilationFinite_word (M : ℕ) (f : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ))
    (hw : w.length ≤ M) :
    annihilationFinite μ M f (creationWord μ w) = wordContraction μ f w := by
  induction w with
  | nil => exact annihilationFinite_vacuum μ M f
  | cons g w ih =>
    rw [annihilationFinite_word_cons μ C M f g w hw, wordContraction_cons,
      ih (by simp only [List.length_cons] at hw; omega)]

end GptLean.PhysicalFock
