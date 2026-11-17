import GptLean.RepresentabilityCoherentBackground

/-! The actual finite-number Segal generator of an imaginary Weyl orbit. -/

noncomputable section
namespace GptLean.WeylPhase

open MeasureTheory GptLean.PhysicalFock GptLean.Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem creationFinite_zero (M : ℕ) (g : Lp ℂ 2 μ) (u : Fock μ) :
    creationFinite μ M g u 0 = 0 := by
  classical
  simp only [creationFinite, sum_apply, lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro n _
  exact lp.single_apply_ne 2 _ _ (by omega)

theorem creationFinite_succ (M n : ℕ) (g : Lp ℂ 2 μ) (u : Fock μ) :
    creationFinite μ M g u (n + 1) =
      if n ≤ M then creationSector μ n g (u n) else 0 := by
  classical
  have hoff (m : ℕ) (h : n ≠ m) : creationBlock μ m g u (n + 1) = 0 :=
    lp.single_apply_ne 2 _ _ (by omega)
  simp only [creationFinite, sum_apply, lp.coeFn_sum, Finset.sum_apply]
  by_cases hn : n ≤ M
  · rw [ite_eq_left hn, Finset.sum_eq_single n]
    · exact lp.single_apply_self 2 (n + 1) _
    · intro m _ hmn
      exact hoff m hmn.symm
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro m hm
    exact hoff m (by have := Finset.mem_range.mp hm; omega)

theorem finite_segalGraph (M : ℕ) (g : Lp ℂ 2 μ) (u : Fock μ)
    (hu : FiniteNumberSupport μ M u) :
    SegalGraph μ g u (creationFinite μ M g u + annihilationFinite μ M g u) := by
  intro n
  have ha (n : ℕ) : annihilationFinite μ M g u n =
      annihilationSector μ n g (u (n + 1)) := by
    rw [annihilationFinite_coordinate]
    split_ifs with hn
    · rfl
    · rw [hu (n + 1) (by omega), map_zero]
  cases n with
  | zero =>
    rw [lp.coeFn_add, Pi.add_apply, creationFinite_zero, zero_add, ha]
    rfl
  | succ n =>
    have hc : creationFinite μ M g u (n + 1) = creationSector μ n g (u n) := by
      rw [creationFinite_succ]
      split_ifs with hn
      · rfl
      · rw [hu n (by omega), map_zero]
    rw [lp.coeFn_add, Pi.add_apply, hc, ha]
    exact add_comm _ _

theorem creationFinite_kernel_smul (M : ℕ) (g : Lp ℂ 2 μ) (c : ℂ) (u : Fock μ) :
    creationFinite μ M (c • g) u = c • creationFinite μ M g u := by
  classical
  simp only [creationFinite, sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n _
  change lp.single 2 (n + 1) (creationSector μ n (c • g) (u n)) =
    c • lp.single 2 (n + 1) (creationSector μ n g (u n))
  rw [creationSector_smul, smul_apply, lp.single_smul]

theorem annihilationFinite_kernel_smul (M : ℕ) (g : Lp ℂ 2 μ) (c : ℂ) (u : Fock μ) :
    annihilationFinite μ M (c • g) u = starRingEnd ℂ c • annihilationFinite μ M g u := by
  classical
  simp only [annihilationFinite, sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n _
  change lp.single 2 n (annihilationSector μ n (c • g) (u (n + 1))) =
    starRingEnd ℂ c • lp.single 2 n (annihilationSector μ n g (u (n + 1)))
  rw [annihilationSector_smul, smul_apply, lp.single_smul]

theorem imaginary_orbit_derivative (W : ConcreteWeylLaw μ) (M : ℕ)
    (g : Lp ℂ 2 μ) (u : Fock μ) (hu : FiniteNumberSupport μ M u) (t : ℝ) :
    HasDerivAt (fun s : ℝ => W.weyl (s • (Complex.I • g)) u)
      (W.weyl (t • (Complex.I • g))
        (Complex.I • (creationFinite μ M g u + annihilationFinite μ M g u))) t := by
  have ht := (hasDerivAt_id t).smul_const (Complex.I • g)
  have h := (W.finite_derivative M u hu (t • (Complex.I • g))).comp_hasDerivAt t ht
  rw [one_smul, finiteWeylDerivative_apply, creationFinite_kernel_smul,
    annihilationFinite_kernel_smul, Complex.conj_I] at h
  have hb : (⟪t • (Complex.I • g), Complex.I • g⟫_ℂ).im = 0 := by
    rw [inner_smul_left_eq_smul]
    simp [← Complex.ofReal_pow]
  simpa only [hb, Complex.ofReal_zero, mul_zero, zero_smul, add_zero,
    neg_smul, sub_neg_eq_add, smul_add, Function.comp_def, id_eq] using h

theorem imaginary_orbit_segalGraph (W : ConcreteWeylLaw μ)
    (g : Lp ℂ 2 μ) (u v : Fock μ) (h : SegalGraph μ g u v) (t : ℝ) :
    SegalGraph μ g (W.weyl (t • (Complex.I • g)) u)
      (W.weyl (t • (Complex.I • g)) v) := by
  have hb : (⟪g, t • (Complex.I • g)⟫_ℂ).re = 0 := by
    rw [inner_smul_right_eq_smul, inner_smul_right]
    simp [← Complex.ofReal_pow]
  simpa only [hb, mul_zero, Complex.ofReal_zero, zero_smul, add_zero] using
    W.field_shift (t • (Complex.I • g)) g u v h

end GptLean.WeylPhase
