import PfHk.PauliSpin

/-! Electron permutations on the concrete spin configurations. Their
covariance with the local Pauli matrices is the algebraic part of the
joint position--spin fermionic symmetry. -/

noncomputable section
namespace PfHk.PauliSpin

open scoped BigOperators
variable {N : ℕ}

/-- Relabel all electron spin coordinates by an electron permutation. -/
def reindex (p : Equiv.Perm (Fin N)) : Equiv.Perm (SpinIndex N) where
  toFun s := s ∘ p
  invFun s := s ∘ p.symm
  left_inv s := by funext n; simp
  right_inv s := by funext n; simp

@[simp] theorem reindex_apply (p : Equiv.Perm (Fin N)) (s : SpinIndex N) (n : Fin N) :
    reindex p s n = s (p n) := rfl

theorem flip_reindex (p : Equiv.Perm (Fin N)) (n : Fin N) (s : SpinIndex N) :
    flip n (reindex p s) = reindex p (flip (p n) s) := by
  funext m
  by_cases h : m = n
  · subst m
    simp only [flip_apply_same, reindex_apply]
    split_ifs <;> simp_all
  · have hp : p m ≠ p n := fun heq => h (p.injective heq)
    simp [flip_apply_ne, h, hp]

@[simp] theorem sign_reindex (p : Equiv.Perm (Fin N)) (n : Fin N) (s : SpinIndex N) :
    sign n (reindex p s) = sign (p n) s := rfl

section Algebra
variable {H : Type*} [AddCommGroup H] [Module ℂ H]

def permuteFamily (p : Equiv.Perm (Fin N)) (u : SpinIndex N → H) : SpinIndex N → H :=
  fun s => u (reindex p s)

omit [AddCommGroup H] [Module ℂ H] in
@[simp] theorem permuteFamily_one (u : SpinIndex N → H) : permuteFamily 1 u = u := rfl

omit [AddCommGroup H] [Module ℂ H] in
theorem permuteFamily_mul (p q : Equiv.Perm (Fin N)) (u : SpinIndex N → H) :
    permuteFamily p (permuteFamily q u) = permuteFamily (p * q) u := rfl

omit [Module ℂ H] in
theorem permuteFamily_add (p : Equiv.Perm (Fin N)) (u v : SpinIndex N → H) :
    permuteFamily p (u + v) = permuteFamily p u + permuteFamily p v := rfl

theorem permuteFamily_smul (p : Equiv.Perm (Fin N)) (c : ℂ) (u : SpinIndex N → H) :
    permuteFamily p (c • u) = c • permuteFamily p u := rfl

/-- Local spin matrices carry the same electron label as the kinetic term. -/
theorem sigmaFamily_permute (p : Equiv.Perm (Fin N)) (n : Fin N) (μ : Fin 3)
    (u : SpinIndex N → H) :
    sigmaFamily (p n) μ (permuteFamily p u) = permuteFamily p (sigmaFamily n μ u) := by
  funext s
  simp only [sigmaFamily, permuteFamily]
  split_ifs <;> simp [flip_reindex]

theorem fieldFamily_permute (p : Equiv.Perm (Fin N)) (n : Fin N) (b : Fin 3 → ℝ)
    (u : SpinIndex N → H) :
    fieldFamily (p n) b (permuteFamily p u) = permuteFamily p (fieldFamily n b u) := by
  funext s
  simp [fieldFamily, permuteFamily, flip_reindex]

end Algebra

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem permuteFamily_inner (p : Equiv.Perm (Fin N)) (u v : SpinIndex N → H) :
    (∑ s, inner ℂ (permuteFamily p u s) (permuteFamily p v s)) =
      ∑ s, inner ℂ (u s) (v s) := by
  exact Fintype.sum_equiv (reindex p) _ _ (fun _ => rfl)

omit [InnerProductSpace ℂ H] in
theorem permuteFamily_sum_norm_sq (p : Equiv.Perm (Fin N)) (u : SpinIndex N → H) :
    (∑ s, ‖permuteFamily p u s‖^2) = ∑ s, ‖u s‖^2 := by
  exact Fintype.sum_equiv (reindex p) _ _ (fun _ => rfl)

end Hilbert
end PfHk.PauliSpin
