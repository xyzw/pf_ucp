import GptLean.ElectronicH1Complex
import GptLean.PhysicalElectronicFermions
import GptLean.SymmetricLift.PermutationMetric

/-!
Particle permutations act isometrically on the actual complex weak H1
graph. The derivative law follows from the distributional identity by
change of variables. Fermionic derivative covariance then follows from
uniqueness of the H1 graph over its L2 value.
-/

noncomputable section

namespace GptLean.PhysicalH1Permutation

open MeasureTheory GptLean.SymmetricLift GptLean.ElectronicH1Complex
open scoped ENNReal ContDiff

set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem pull_test_integral (π : Equiv.Perm (Fin N))
    (v : PhysicalElectronicFermions.FullSpace N H) (φ : Configuration N → ℝ) :
    (∫ x, φ x • PhysicalElectronicFermions.permutation N H π v x) =
      ∫ z, φ ((permuteConfiguration π).symm z) • v z := by
  calc
    _ = ∫ x, φ ((permuteConfiguration π).symm (permuteConfiguration π x)) •
        v (permuteConfiguration π x) := by
      apply integral_congr_ae
      filter_upwards [PhysicalElectronicFermions.permutation_ae N H π v] with x hx
      rw [hx]
      simp
    _ = _ := (permuteConfiguration π).measurePreserving.integral_comp
      (permuteConfiguration π).toMeasurableEquiv.measurableEmbedding
      (fun z => φ ((permuteConfiguration π).symm z) • v z)

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
theorem pull_test_fderiv (π : Equiv.Perm (Fin N)) (q : Fin N × Fin 3)
    (φ : Configuration N → ℝ) (hφ : ContDiff ℝ ∞ φ) (z : Configuration N) :
    fderiv ℝ (φ ∘ (permuteConfiguration π).symm) z
      (EuclideanSpace.single (π q.1, q.2) 1) =
        fderiv ℝ φ ((permuteConfiguration π).symm z) (EuclideanSpace.single q 1) := by
  have hd : (permuteConfiguration π).symm
      (EuclideanSpace.single (π q.1, q.2) 1) = EuclideanSpace.single q 1 := by
    rw [← permuteConfiguration_single π q]
    exact (permuteConfiguration π).symm_apply_apply _
  have hh : fderiv ℝ (φ ∘ (permuteConfiguration π).symm) z =
      (fderiv ℝ φ ((permuteConfiguration π).symm z)).comp
        (permuteConfiguration π).symm.toContinuousLinearEquiv.toContinuousLinearMap :=
    ((hφ.differentiable (by simp) _).hasFDerivAt.comp z
      (permuteConfiguration π).symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
  rw [hh]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, hd]

variable [CompleteSpace H]

theorem weak_permutation (π : Equiv.Perm (Fin N))
    (u : ComplexH1 H (Fin N × Fin 3)) :
    HasWeakH1Local (PhysicalElectronicFermions.permutation N H π (value u))
      (fun q => PhysicalElectronicFermions.permutation N H π
        (derivative (π q.1, q.2) u)) := by
  refine ⟨fun K _ => (Lp.memLp _).restrict K, fun q K _ => (Lp.memLp _).restrict K, ?_⟩
  intro q φ hφ hs
  rw [pull_test_integral, pull_test_integral]
  have htest : ContDiff ℝ ∞ (φ ∘ (permuteConfiguration π).symm) :=
    hφ.comp (permuteConfiguration π).symm.toContinuousLinearEquiv.contDiff
  have hcompact : HasCompactSupport (φ ∘ (permuteConfiguration π).symm) :=
    hs.comp_homeomorph (permuteConfiguration π).symm.toHomeomorph
  have hw := (weak u).weak (π q.1, q.2) _ htest hcompact
  simpa only [Function.comp_apply, pull_test_fderiv π q φ hφ] using hw

def permuted (π : Equiv.Perm (Fin N)) (u : ComplexH1 H (Fin N × Fin 3)) :
    ComplexH1 H (Fin N × Fin 3) :=
  ⟨(PhysicalElectronicFermions.permutation N H π (value u),
      fun q => PhysicalElectronicFermions.permutation N H π (derivative (π q.1, q.2) u)),
    weak_permutation π u⟩

@[simp] theorem value_permuted (π : Equiv.Perm (Fin N))
    (u : ComplexH1 H (Fin N × Fin 3)) :
    value (permuted π u) = PhysicalElectronicFermions.permutation N H π (value u) := rfl

@[simp] theorem derivative_permuted (π : Equiv.Perm (Fin N))
    (u : ComplexH1 H (Fin N × Fin 3)) (q : Fin N × Fin 3) :
    derivative q (permuted π u) =
      PhysicalElectronicFermions.permutation N H π (derivative (π q.1, q.2) u) := rfl

theorem norm_gradient_permuted (π : Equiv.Perm (Fin N))
    (u : ComplexH1 H (Fin N × Fin 3)) : ‖gradient (permuted π u)‖ = ‖gradient u‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro q
    change ‖PhysicalElectronicFermions.permutation N H π
      (derivative (π q.1, q.2) u)‖ ≤ _
    rw [(PhysicalElectronicFermions.permutation N H π).norm_map]
    exact norm_le_pi_norm (gradient u) (π q.1, q.2)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro q
    have h := norm_le_pi_norm (gradient (permuted π u)) (π.symm q.1, q.2)
    change ‖PhysicalElectronicFermions.permutation N H π
      (derivative (π (π.symm q.1), q.2) u)‖ ≤ _ at h
    change ‖derivative q u‖ ≤ _
    simpa only [(PhysicalElectronicFermions.permutation N H π).norm_map,
      π.apply_symm_apply, Prod.mk.eta] using h

/-- The physical particle pullback on the complete complex H1 graph. -/
def permutation (π : Equiv.Perm (Fin N)) :
    ComplexH1 H (Fin N × Fin 3) →ₗᵢ[ℂ] ComplexH1 H (Fin N × Fin 3) where
  toFun := permuted π
  map_add' u v := value_injective (by simp only [value_permuted, map_add])
  map_smul' c u := value_injective (by simp only [value_permuted, map_smul, RingHom.id_apply])
  norm_map' u := by
    change ‖permuted π u‖ = ‖u‖
    calc
      _ = max ‖value (permuted π u)‖ ‖gradient (permuted π u)‖ := rfl
      _ = max ‖value u‖ ‖gradient u‖ := by
        rw [value_permuted, (PhysicalElectronicFermions.permutation N H π).norm_map,
          norm_gradient_permuted]
      _ = _ := rfl

@[simp] theorem value_permutation (π : Equiv.Perm (Fin N))
    (u : ComplexH1 H (Fin N × Fin 3)) :
    value (permutation π u) = PhysicalElectronicFermions.permutation N H π (value u) := rfl

@[simp] theorem derivative_permutation (π : Equiv.Perm (Fin N))
    (u : ComplexH1 H (Fin N × Fin 3)) (q : Fin N × Fin 3) :
    derivative q (permutation π u) =
      PhysicalElectronicFermions.permutation N H π (derivative (π q.1, q.2) u) := rfl

theorem fermionic_permutation (u : ComplexH1 H (Fin N × Fin 3))
    (hu : value u ∈ PhysicalElectronicFermions.fermionicSubspace N H)
    (π : Equiv.Perm (Fin N)) :
    permutation π u = PhysicalElectronicFermions.signCharacter N π • u := by
  apply value_injective
  rw [value_permutation, map_smul]
  exact hu π

/-- Ordinary electronic derivatives have the exact fermionic covariance
needed by the physical summed current identity. -/
theorem fermionic_derivative_ae (u : ComplexH1 H (Fin N × Fin 3))
    (hu : value u ∈ PhysicalElectronicFermions.fermionicSubspace N H)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3) :
    ∀ᵐ x ∂volume, derivative (i, a) u (permuteConfiguration π x) =
      PhysicalElectronicFermions.signCharacter N π • derivative (π.symm i, a) u x := by
  have hc := congrArg (derivative (π.symm i, a)) (fermionic_permutation u hu π)
  simp only [derivative_permutation, map_smul, π.apply_symm_apply] at hc
  filter_upwards [PhysicalElectronicFermions.permutation_ae N H π (derivative (i, a) u),
    Lp.coeFn_smul (PhysicalElectronicFermions.signCharacter N π)
      (derivative (π.symm i, a) u)] with x hp hs
  have hx := congrArg (fun v : PhysicalElectronicFermions.FullSpace N H => v x) hc
  rw [hp, hs] at hx
  exact hx

end GptLean.PhysicalH1Permutation
