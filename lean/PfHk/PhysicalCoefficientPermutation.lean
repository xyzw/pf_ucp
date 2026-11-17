import PfHk.PhysicalCommonFormCoefficients
import GptLean.SymmetricLift.PermutationMetric

/-! Identical one-body coefficients and the actual repulsive Coulomb
sum have the exact permutation laws required by fermionic reduction. -/

noncomputable section
namespace PfHk.PhysicalCoefficientPermutation

open GptLean GptLean.SymmetricLift GptLean.PhysicalPairDuality
  PfHk.CoordinateSobolev
  PfHk.PhysicalCommonFormDomain

set_option Elab.async false
set_option maxHeartbeats 30000

private theorem twice_upper_sum {J : Type*} [Fintype J] [LinearOrder J]
    (f : J → J → ℝ) (hsym : ∀ i j, f i j = f j i) :
    2 * (∑ i, ∑ j, if i < j then f i j else 0) =
      ∑ i, ∑ j, if i ≠ j then f i j else 0 := by
  classical
  have hswap : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [hsym]
  calc
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by rw [hswap]; ring
    _ = ∑ i, ∑ j, ((if i < j then f i j else 0) +
        (if j < i then f i j else 0)) := by simp only [Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rcases lt_trichotomy i j with h | h | h
      · simp only [ite_eq_left h, ite_eq_right (not_lt_of_ge h.le),
          ite_eq_left (ne_of_lt h), add_zero]
      · subst j
        simp only [lt_self_iff_false, ne_eq, not_true_eq_false, ite_false, add_zero]
      · simp only [ite_eq_right (not_lt_of_ge h.le), ite_eq_left h,
          ite_eq_left (ne_of_gt h), zero_add]

variable {N : ℕ}

theorem coulomb_permutation (π : Equiv.Perm (Fin N)) (X : Configuration N) :
    PhysicalCoulombH1.potential N (permuteConfiguration π X) =
      PhysicalCoulombH1.potential N X := by
  let f : Fin N → Fin N → ℝ := fun i j => ‖particle X i - particle X j‖⁻¹
  let fπ : Fin N → Fin N → ℝ := fun i j =>
    ‖particle (permuteConfiguration π X) i - particle (permuteConfiguration π X) j‖⁻¹
  have hs : ∀ i j, f i j = f j i := fun i j => congrArg (fun r : ℝ => r⁻¹) (norm_sub_rev _ _)
  have hsπ : ∀ i j, fπ i j = fπ j i := fun i j => congrArg (fun r : ℝ => r⁻¹) (norm_sub_rev _ _)
  have hsum : (∑ i, ∑ j, if i ≠ j then fπ i j else 0) =
      ∑ i, ∑ j, if i ≠ j then f i j else 0 := by
    let g : Fin N → Fin N → ℝ := fun i j => if i ≠ j then f i j else 0
    have hreindex : (∑ i, ∑ j, g (π.symm i) (π.symm j)) = ∑ i, ∑ j, g i j :=
      (Finset.sum_congr rfl fun i _ => π.symm.sum_comp (g (π.symm i))).trans
        (π.symm.sum_comp (fun i => ∑ j, g i j))
    simpa only [g, fπ, f, particle_permute, ne_eq, Equiv.apply_eq_iff_eq] using hreindex
  have hdouble := (twice_upper_sum fπ hsπ).trans (hsum.trans (twice_upper_sum f hs).symm)
  change 2 * PhysicalCoulombH1.potential N (permuteConfiguration π X) =
    2 * PhysicalCoulombH1.potential N X at hdouble
  exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hdouble

theorem coordinate_permutation (π : Equiv.Perm (Fin N)) (n : Fin N)
    (b : PhysicalSourceCoordinates.Position → ℝ) (X : Configuration N) :
    coordinateCoefficient n b (permuteConfiguration π X) =
      coordinateCoefficient (π.symm n) b X := by
  apply congrArg b
  ext i
  rfl

theorem vector_permutation (A : VectorPotential) (π : Equiv.Perm (Fin N))
    (q : Fin N × Fin 3) (X : Configuration N) :
    vector A q (permuteConfiguration π X) = vector A (π.symm q.1, q.2) X :=
  coordinate_permutation π q.1 (fun x => A.val x q.2) X

theorem scalar_permutation (v : ScalarPotential) (c : ℝ)
    (π : Equiv.Perm (Fin N)) (X : Configuration N) :
    scalar v c (permuteConfiguration π X) = scalar v c X := by
  unfold scalar
  exact congrArg₂ (· + ·)
    ((Finset.sum_congr rfl fun n _ => coordinate_permutation π n v.val X).trans
      (π.symm.sum_comp (fun n => coordinateCoefficient n v.val X)))
    (congrArg (c * ·) (coulomb_permutation π X))

theorem positive_permutation (v : ScalarPotential) (c : ℝ)
    (π : Equiv.Perm (Fin N)) (X : Configuration N) :
    positive v c (permuteConfiguration π X) = positive v c X :=
  congrArg (fun r : ℝ => Real.sqrt (max r 0)) (scalar_permutation v c π X)

theorem negative_permutation (v : ScalarPotential) (c : ℝ)
    (π : Equiv.Perm (Fin N)) (X : Configuration N) :
    negative v c (permuteConfiguration π X) = negative v c X :=
  congrArg (fun r : ℝ => Real.sqrt (max (-r) 0)) (scalar_permutation v c π X)

end PfHk.PhysicalCoefficientPermutation
