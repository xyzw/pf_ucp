import GptLean.SymmetricLift.Configuration
import Mathlib.Tactic.Positivity

/-! Direct bounds relating the centered radius to pair interaction energy. -/
noncomputable section
namespace GptLean.SymmetricLift
open scoped BigOperators
open WithLp

def particle {N : ℕ} (x : Configuration N) (i : Fin N) : EuclideanSpace ℝ (Fin 3) :=
  toLp 2 (fun μ => x (i, μ))

def meanParticle {N : ℕ} (x : Configuration N) : EuclideanSpace ℝ (Fin 3) :=
  toLp 2 (meanCoordinate x)

theorem particle_center {N : ℕ} (x : Configuration N) (i : Fin N) :
    particle (center N x) i = particle x i - meanParticle x := by
  ext μ
  exact center_apply x (i, μ)

theorem particle_norm_le {N : ℕ} (x : Configuration N) (i : Fin N) :
    ‖particle x i‖ ≤ ‖x‖ := by
  have hsq : ‖particle x i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fintype.sum_prod_type]
    exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun μ _ => sq_nonneg (x (j, μ))))
      (Finset.mem_univ i)
  nlinarith [norm_nonneg (particle x i), norm_nonneg x]

theorem particle_mean_distance_le_radius {N : ℕ} (x : Configuration N) (i : Fin N) :
    ‖particle x i - meanParticle x‖ ≤ ‖center N x‖ := by
  rw [← particle_center]
  exact particle_norm_le _ _

def pairDistance {N : ℕ} (x : Configuration N) (i j : Fin N) : ℝ :=
  ‖particle x i - particle x j‖

theorem pairDistance_le_two_radius {N : ℕ} (x : Configuration N) (i j : Fin N) :
    pairDistance x i j ≤ 2 * ‖center N x‖ := by
  have heq : particle x i - particle x j =
      particle (center N x) i - particle (center N x) j := by
    rw [particle_center, particle_center]
    abel
  calc
    pairDistance x i j = ‖particle (center N x) i - particle (center N x) j‖ := congrArg norm heq
    _ ≤ ‖particle (center N x) i‖ + ‖particle (center N x) j‖ := norm_sub_le _ _
    _ ≤ 2 * ‖center N x‖ := by
      linarith [particle_norm_le (center N x) i, particle_norm_le (center N x) j]

theorem pairDistance_pos_of_distinct {N : ℕ} {x : Configuration N}
    (hx : x ∈ distinctConfigurations N) {i j : Fin N} (hij : i ≠ j) :
    0 < pairDistance x i j := by
  apply norm_pos_iff.mpr
  intro h
  have heq := sub_eq_zero.mp h
  obtain ⟨μ, hμ⟩ := hx i j hij
  exact hμ (congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y μ) heq)

/-- Each unordered pair is counted once. -/
def pairEnergy {N : ℕ} (x : Configuration N) : ℝ :=
  ∑ i, ∑ j, if i < j then (pairDistance x i j ^ 2)⁻¹ else 0

theorem pairEnergy_nonneg {N : ℕ} (x : Configuration N) : 0 ≤ pairEnergy x := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

theorem pairEnergy_term_le {N : ℕ} (x : Configuration N) {i j : Fin N} (hij : i < j) :
    (pairDistance x i j ^ 2)⁻¹ ≤ pairEnergy x := by
  have hinner : (pairDistance x i j ^ 2)⁻¹ ≤
      ∑ k, if i < k then (pairDistance x i k ^ 2)⁻¹ else 0 := by
    simpa only [if_pos hij] using
      (Finset.single_le_sum (s := Finset.univ) (a := j)
        (f := fun k => if i < k then (pairDistance x i k ^ 2)⁻¹ else 0)
        (fun k _ => by split_ifs <;> positivity) (Finset.mem_univ j))
  apply hinner.trans
  unfold pairEnergy
  apply Finset.single_le_sum (a := i)
  · intro k _
    apply Finset.sum_nonneg
    intro l _
    split_ifs <;> positivity
  · exact Finset.mem_univ i

/-- A nonoptimized constant avoids needing an exact variance identity.
The theorem in the article leaves its particle-number constant unspecified. -/
theorem radius_inverse_sq_le_pairEnergy {N : ℕ} (hN : 2 ≤ N)
    {x : Configuration N} (hx : x ∈ distinctConfigurations N) :
    (‖center N x‖ ^ 2)⁻¹ ≤ 4 * pairEnergy x := by
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨1, by omega⟩
  have hij : i < j := by change (0 : ℕ) < 1; omega
  have hd := pairDistance_pos_of_distinct hx (ne_of_lt hij)
  have hr : 0 < ‖center N x‖ := norm_pos_iff.mpr (center_ne_zero_of_distinct hN hx)
  have hb := pairDistance_le_two_radius x i j
  have hsq : pairDistance x i j ^ 2 ≤ 4 * ‖center N x‖ ^ 2 := by nlinarith
  have hi : (‖center N x‖ ^ 2)⁻¹ ≤ 4 * (pairDistance x i j ^ 2)⁻¹ := by
    rw [← one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (sq_pos_of_pos hr) (sq_pos_of_pos hd)).mpr
    simpa only [one_mul] using hsq
  exact hi.trans (mul_le_mul_of_nonneg_left (pairEnergy_term_le x hij) (by norm_num))

theorem pairDistance_symm {N : ℕ} (x : Configuration N) (i j : Fin N) :
    pairDistance x i j = pairDistance x j i := norm_sub_rev _ _

theorem pairEnergy_twice {N : ℕ} (x : Configuration N) :
    2 * pairEnergy x = ∑ i, ∑ j, if i ≠ j then (pairDistance x i j ^ 2)⁻¹ else 0 := by
  have hswap : (∑ i, ∑ j, if j < i then (pairDistance x j i ^ 2)⁻¹ else 0) =
      pairEnergy x := by rw [Finset.sum_comm]; rfl
  calc
    2 * pairEnergy x = pairEnergy x + pairEnergy x := by ring
    _ = ∑ i, ∑ j, ((if i < j then (pairDistance x i j ^ 2)⁻¹ else 0) +
        (if j < i then (pairDistance x j i ^ 2)⁻¹ else 0)) := by
      simp only [Finset.sum_add_distrib, hswap]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rcases lt_trichotomy i j with h | h | h
      · simp [h, ne_of_lt h, not_lt_of_ge (le_of_lt h)]
      · subst j; simp
      · simp [h, (ne_of_gt h), not_lt_of_ge (le_of_lt h), pairDistance_symm x j i]

/-- Block enumeration may reverse the order of particles. Passing through
the symmetric ordered-pair sum proves monotonicity for every injection. -/
theorem pairEnergy_embedding {M N : ℕ} (x : Configuration M) (y : Configuration N)
    (f : Fin M ↪ Fin N) (hp : ∀ i, particle x i = particle y (f i)) :
    pairEnergy x ≤ pairEnergy y := by
  have he : Function.Injective (fun p : Fin M × Fin M => (f p.1, f p.2)) := by
    intro p q h
    exact Prod.ext (f.injective (congrArg Prod.fst h)) (f.injective (congrArg Prod.snd h))
  have ho : (∑ p : Fin M × Fin M,
      if p.1 ≠ p.2 then (pairDistance x p.1 p.2 ^ 2)⁻¹ else 0) ≤
      ∑ p : Fin N × Fin N,
        if p.1 ≠ p.2 then (pairDistance y p.1 p.2 ^ 2)⁻¹ else 0 := by
    apply Finset.sum_le_sum_of_injOn (fun p : Fin M × Fin M => (f p.1, f p.2)) he.injOn
      (Finset.subset_univ _)
    · intro p _
      simp only [pairDistance, hp, ne_eq, f.injective.eq_iff]
      exact le_rfl
    · intro p _ _
      split_ifs <;> positivity
  simp only [Fintype.sum_prod_type] at ho
  rw [← pairEnergy_twice x, ← pairEnergy_twice y] at ho
  linarith

/-- Passing from operator derivative norms to the sum over the 3N Cartesian
directions costs at most the dimension of configuration space. -/
theorem coordinate_partition_bound {N : ℕ} {ι : Type*} [Fintype ι]
    (L : ι → Configuration N →L[ℝ] ℝ) :
    (∑ q : Fin N × Fin 3, ∑ a, (L a (EuclideanSpace.single q 1)) ^ 2) ≤
      ((N : ℝ) * 3) * ∑ a, ‖L a‖ ^ 2 := by
  have h (a : ι) (q : Fin N × Fin 3) :
      (L a (EuclideanSpace.single q 1)) ^ 2 ≤ ‖L a‖ ^ 2 := by
    have hn : ‖L a (EuclideanSpace.single q 1)‖ ≤ ‖L a‖ := by
      simpa using (L a).le_opNorm (EuclideanSpace.single q 1)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    simpa using hs
  calc
    _ ≤ ∑ _q : Fin N × Fin 3, ∑ a, ‖L a‖ ^ 2 :=
      Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun a _ => h a q))
    _ = _ := by simp [Fintype.card_prod]

end GptLean.SymmetricLift
