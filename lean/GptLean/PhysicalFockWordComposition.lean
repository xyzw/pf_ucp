import GptLean.PhysicalFockSplitCoassociation

/-!
The retained observable polynomial composes exactly when the actual
one-photon components coassociate. This is proved on finite creation
words and uses the isometry of the matched exponential map to sum out
the two environmental factors. No channel composition is assumed.
-/

noncomputable section
namespace GptLean.PhysicalFock.SplitCoassociation

open MeasureTheory PhotonLocalizationFockChannel TensorCoordinates
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

private theorem list_sum_swap {α β E : Type*} [AddCommMonoid E]
    (s : List α) (t : List β) (f : α → β → E) :
    (s.map (fun a => (t.map (f a)).sum)).sum =
      (t.map (fun b => (s.map (fun a => f a b)).sum)).sum := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.map_cons, List.sum_cons, List.sum_map_add]
    exact congrArg (fun x => (t.map (f a)).sum + x) ih

omit [SigmaFinite μ] in
theorem eval_congr
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) {E : Type*} [AddCommMonoid E]
    {F G : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ) → E}
    (h : ∀ p, F p = G p) : eval μ j w F = eval μ j w G :=
  congrArg (eval μ j w) (funext h)

omit [SigmaFinite μ] in
theorem eval_comm
    (j k : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w z : List (Lp ℂ 2 μ)) {E : Type*} [AddCommMonoid E]
    (F : (List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ)) →
      (List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ)) → E) :
    eval μ j w (fun p => eval μ k z (fun q => F p q)) =
      eval μ k z (fun q => eval μ j w (fun p => F p q)) :=
  list_sum_swap _ _ F

omit [SigmaFinite μ] in
theorem eval_mul_left
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) (c : ℂ)
    (F : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ) → ℂ) :
    eval μ j w (fun p => c * F p) = c * eval μ j w F :=
  List.sum_map_mul_left (splitAssignments μ j w) F c

omit [SigmaFinite μ] in
theorem eval_mul_right
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) (c : ℂ)
    (F : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ) → ℂ) :
    eval μ j w (fun p => F p * c) = eval μ j w F * c :=
  List.sum_map_mul_right (splitAssignments μ j w) F c

private theorem inner_list_sum_left {H α : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (s : List α) (f : α → H) (v : H) :
    ⟪(s.map f).sum, v⟫_ℂ = (s.map (fun a => ⟪f a, v⟫_ℂ)).sum := by
  induction s with
  | nil => simp
  | cons a s ih => simp only [List.map_cons, List.sum_cons, inner_add_left, ih]

private theorem inner_list_sum_right {H α : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (s : List α) (f : α → H) (v : H) :
    ⟪v, (s.map f).sum⟫_ℂ = (s.map (fun a => ⟪v, f a⟫_ℂ)).sum := by
  induction s with
  | nil => simp
  | cons a s ih => simp only [List.map_cons, List.sum_cons, inner_add_right, ih]

def wordGram (w z : List (Lp ℂ 2 μ)) : ℂ :=
  ⟪creationWord μ w, creationWord μ z⟫_ℂ

def couple
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (S : List (Lp ℂ 2 μ) → List (Lp ℂ 2 μ) → ℂ)
    (w z : List (Lp ℂ 2 μ)) : ℂ :=
  eval μ j w (fun p => eval μ j z (fun q => S p.1 q.1 * wordGram μ p.2 q.2))

theorem couple_wordGram (B : ConcreteExponentialLaw μ)
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w z : List (Lp ℂ 2 μ)) :
    couple μ j (wordGram μ) w z = wordGram μ w z := by
  have h := (B.split μ j).inner_map_map (creationWord μ w) (creationWord μ z)
  rw [B.split_word, B.split_word, splitCreationTensor, splitCreationTensor,
    inner_list_sum_left] at h
  simpa only [inner_list_sum_right, tensor_inner, couple, eval, wordGram] using h

theorem couple_observable (B : ConcreteExponentialLaw μ)
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (A : Fock μ →L[ℂ] Fock μ) (w z : List (Lp ℂ 2 μ)) :
    couple μ j (fun a b => ⟪creationWord μ a, A (creationWord μ b)⟫_ℂ) w z =
      ⟪B.split μ j (creationWord μ w),
        retainedOperator A (B.split μ j (creationWord μ z))⟫_ℂ := by
  simp only [B.split_word, splitCreationTensor, map_list_sum, List.map_map,
    inner_list_sum_left, inner_list_sum_right, Function.comp_def,
    retainedOperator_tensor, tensor_inner, couple, eval, wordGram]
  exact list_sum_swap _ _ _

theorem couple_comp (B : ConcreteExponentialLaw μ)
    (j k : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (h₁ : ∀ f, retainedMap j (retainedMap k f) = retainedMap j f)
    (h₂ : ∀ f, discardedMap μ j (retainedMap k f) = retainedMap k (discardedMap μ j f))
    (h₃ : ∀ f, discardedMap μ k f = discardedMap μ k (discardedMap μ j f))
    (S : List (Lp ℂ 2 μ) → List (Lp ℂ 2 μ) → ℂ)
    (w z : List (Lp ℂ 2 μ)) :
    couple μ k (couple μ j S) w z = couple μ j S w z := by
  change eval μ k w (fun p => eval μ k z (fun q =>
      couple μ j S p.1 q.1 * wordGram μ p.2 q.2)) = _
  calc
    _ = eval μ k w (fun p => eval μ j p.1 (fun a =>
        eval μ k z (fun q => eval μ j q.1 (fun b =>
          S a.1 b.1 * wordGram μ a.2 b.2 * wordGram μ p.2 q.2)))) := by
      apply eval_congr
      intro p
      simp_rw [couple, ← eval_mul_right]
      exact eval_comm μ k j z p.1 _
    _ = eval μ j w (fun p => eval μ k p.2 (fun a =>
        eval μ k z (fun q => eval μ j q.1 (fun b =>
          S p.1 b.1 * wordGram μ a.1 b.2 * wordGram μ a.2 q.2)))) :=
      eval_coassociate μ j k h₁ h₂ h₃ w (fun a b c =>
        eval μ k z (fun q => eval μ j q.1 (fun d =>
          S a d.1 * wordGram μ b d.2 * wordGram μ c q.2)))
    _ = eval μ j w (fun p => eval μ k p.2 (fun a =>
        eval μ j z (fun q => eval μ k q.2 (fun b =>
          S p.1 q.1 * wordGram μ a.1 b.1 * wordGram μ a.2 b.2)))) := by
      apply eval_congr
      intro p
      apply eval_congr
      intro a
      exact eval_coassociate μ j k h₁ h₂ h₃ z (fun b c d =>
        S p.1 b * wordGram μ a.1 c * wordGram μ a.2 d)
    _ = eval μ j w (fun p => eval μ j z (fun q =>
        eval μ k p.2 (fun a => eval μ k q.2 (fun b =>
          S p.1 q.1 * wordGram μ a.1 b.1 * wordGram μ a.2 b.2)))) := by
      apply eval_congr
      intro p
      exact eval_comm μ k j p.2 z _
    _ = couple μ j S w z := by
      apply eval_congr
      intro p
      apply eval_congr
      intro q
      simp_rw [mul_assoc, eval_mul_left]
      rw [← couple, couple_wordGram μ B]

end GptLean.PhysicalFock.SplitCoassociation
