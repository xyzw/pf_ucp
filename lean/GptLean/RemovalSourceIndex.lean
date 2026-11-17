import GptLean.RemovalSource

/-!
Countable localization families are embedded into the natural numbers
and padded by zero. This also handles finite label types, including the
single lattice label when the particle index is empty.
-/

noncomputable section

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Function

variable {A X : Type*}

def zeroPad (e : A ↪ ℕ) (f : A → X → ℝ) : ℕ → X → ℝ :=
  Function.extend e f 0

@[simp] theorem zeroPad_apply (e : A ↪ ℕ) (f : A → X → ℝ) (a : A) :
    zeroPad e f (e a) = f a := e.injective.extend_apply f 0 a

theorem zeroPad_off_range (e : A ↪ ℕ) (f : A → X → ℝ) {n : ℕ}
    (hn : ¬ ∃ a, e a = n) : zeroPad e f n = 0 :=
  Function.extend_apply' (f := e) f (0 : ℕ → X → ℝ) n hn

theorem zeroPad_cases (e : A ↪ ℕ) (f : A → X → ℝ) (n : ℕ) :
    zeroPad e f n = 0 ∨ ∃ a, zeroPad e f n = f a := by
  classical
  by_cases h : ∃ a, e a = n
  · rcases h with ⟨a, rfl⟩
    exact Or.inr ⟨a, zeroPad_apply e f a⟩
  · exact Or.inl (zeroPad_off_range e f h)

theorem zeroPad_map {Y : Type*} [Zero Y] (e : A ↪ ℕ) (f : A → X → ℝ)
    (F : (X → ℝ) → Y) (hF : F 0 = 0) (n : ℕ) :
    F (zeroPad e f n) = Function.extend e (fun a => F (f a)) 0 n := by
  classical
  by_cases h : ∃ a, e a = n
  · rcases h with ⟨a, rfl⟩
    rw [zeroPad_apply, e.injective.extend_apply]
  · rw [zeroPad_off_range e f h, hF,
      Function.extend_apply' (f := e) (fun a => F (f a)) (0 : ℕ → Y) n h]
    rfl

theorem zeroPad_partition (e : A ↪ ℕ) (f : A → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1) (x : X) :
    HasSum (fun n => zeroPad e f n x ^ 2) 1 := by
  have he : (fun n => zeroPad e f n x ^ 2) =
      Function.extend e (fun a => f a x ^ 2) 0 :=
    funext (zeroPad_map e f (fun g => g x ^ 2) (by simp))
  rw [he]
  exact (hasSum_extend_zero e.injective).mpr (hpart x)

theorem zeroPad_nonneg (e : A ↪ ℕ) (f : A → X → ℝ)
    (hf : ∀ a x, 0 ≤ f a x) (n : ℕ) (x : X) : 0 ≤ zeroPad e f n x := by
  rcases zeroPad_cases e f n with h | ⟨a, h⟩
  · rw [h]
    exact le_refl 0
  · rw [h]
    exact hf a x

theorem zeroPad_locallyFinite [TopologicalSpace X] (e : A ↪ ℕ) (f : A → X → ℝ)
    (hf : LocallyFinite (fun a => Function.support (f a))) :
    LocallyFinite (fun n => Function.support (zeroPad e f n)) := by
  intro x
  obtain ⟨s, hs, hfin⟩ := hf x
  refine ⟨s, hs, (hfin.image e).subset ?_⟩
  intro n hn
  classical
  by_cases h : ∃ a, e a = n
  · rcases h with ⟨a, rfl⟩
    exact ⟨a, by simpa only [Set.mem_setOf_eq, zeroPad_apply] using hn, rfl⟩
  · have hz := zeroPad_off_range e f h
    simpa only [Set.mem_setOf_eq, hz, Function.support_zero, Set.empty_inter,
      Set.not_nonempty_empty] using hn

theorem zeroPad_measurable [MeasurableSpace X] {ν : Measure X}
    (e : A ↪ ℕ) (f : A → X → ℝ) (hf : ∀ a, AEStronglyMeasurable (f a) ν) (n : ℕ) :
    AEStronglyMeasurable (zeroPad e f n) ν := by
  rcases zeroPad_cases e f n with h | ⟨a, h⟩
  · rw [h]
    exact aestronglyMeasurable_zero
  · rw [h]
    exact hf a

section Differentiable

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem zeroPad_differentiable (e : A ↪ ℕ) (f : A → X → ℝ)
    (hf : ∀ a, Differentiable ℝ (f a)) (n : ℕ) : Differentiable ℝ (zeroPad e f n) := by
  rcases zeroPad_cases e f n with h | ⟨a, h⟩
  · rw [h]
    exact differentiable_const 0
  · rw [h]
    exact hf a

theorem zeroPad_metric (e : A ↪ ℕ) (f : A → X → ℝ) (x v : X) :
    (∑' n, fderiv ℝ (zeroPad e f n) x v ^ 2) = ∑' a, fderiv ℝ (f a) x v ^ 2 := by
  have he : (fun n => fderiv ℝ (zeroPad e f n) x v ^ 2) =
      Function.extend e (fun a => fderiv ℝ (f a) x v ^ 2) 0 :=
    funext (zeroPad_map e f (fun g => fderiv ℝ g x v ^ 2) (by simp))
  rw [he, tsum_extend_zero e.injective]

theorem zeroPad_derivative_measurable [MeasurableSpace X] {ν : Measure X}
    (e : A ↪ ℕ) (f : A → X → ℝ) (v : X)
    (hf : ∀ a, AEStronglyMeasurable (fun x => fderiv ℝ (f a) x v) ν) (n : ℕ) :
    AEStronglyMeasurable (fun x => fderiv ℝ (zeroPad e f n) x v) ν := by
  rcases zeroPad_cases e f n with h | ⟨a, h⟩
  · have he : (fun x => fderiv ℝ (zeroPad e f n) x v) = fun _ : X => (0 : ℝ) := by
      ext x
      simp [h]
    rw [he]
    exact aestronglyMeasurable_const
  · simpa only [h] using hf a

end Differentiable

/-- An embedding exists for every countable label type, without an
infinitude or a nonempty-index hypothesis. -/
def countableIndex (A : Type*) [Countable A] : A ↪ ℕ :=
  ⟨Classical.choose (exists_injective_nat A), Classical.choose_spec (exists_injective_nat A)⟩

end GptLean.RemovalSource
