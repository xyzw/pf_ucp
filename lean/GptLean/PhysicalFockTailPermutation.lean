import GptLean.PhysicalFockCreation

/-!
Contraction of a symmetric sector leaves a symmetric tail.

The proof uses the actual coordinate permutations and tensor insertion,
then Hilbert adjointness. This identifies annihilation with contraction
without inserting an unproved symmetry premise into the slice calculus.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

def tailPermutation {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  ((finSuccEquiv n).trans (Equiv.optionCongr π)).trans (finSuccEquiv n).symm

@[simp] theorem tailPermutation_zero {n : ℕ} (π : Equiv.Perm (Fin n)) :
    tailPermutation π 0 = 0 := by simp [tailPermutation]

@[simp] theorem tailPermutation_succ {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    tailPermutation π i.succ = (π i).succ := by simp [tailPermutation]

@[simp] theorem tailPermutation_symm_zero {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (tailPermutation π).symm 0 = 0 := by simp [tailPermutation, Equiv.optionCongr]

@[simp] theorem tailPermutation_symm_succ {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (tailPermutation π).symm i.succ = (π.symm i).succ := by simp [tailPermutation, Equiv.optionCongr]

private theorem permutationCoordinates_apply {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n → Ω) (i : Fin n) :
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π k i = k (π.symm i) := by
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem tensorInsertion_tailPermutation (n : ℕ) (π : Equiv.Perm (Fin n))
    (f : Lp ℂ 2 μ) (v : FullSector μ n) :
    tensorInsertion μ n f (permutation μ n π v) =
      permutation μ (n + 1) (tailPermutation π) (tensorInsertion μ n f v) := by
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
  have htail := hp.quasiMeasurePreserving.ae
    ((Measure.quasiMeasurePreserving_snd (μ := μ)).ae (permutation_ae μ n π v))
  have hlift := measurePreserving_piCongrLeft (fun _ : Fin (n + 1) => μ) (tailPermutation π)
  apply Lp.ext
  filter_upwards [tensorInsertion_ae μ n f (permutation μ n π v),
    permutation_ae μ (n + 1) (tailPermutation π) (tensorInsertion μ n f v),
    hlift.quasiMeasurePreserving.ae (tensorInsertion_ae μ n f v), htail]
      with k ha hb hc hd
  rw [ha, hb, Function.comp_apply, hc]
  change (permutation μ n π v) (fun i => k i.succ) =
    v (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π (fun i => k i.succ)) at hd
  rw [hd]
  simp only [permutationCoordinates_apply, tailPermutation_symm_zero, tailPermutation_symm_succ]
  exact congrArg (fun t : Fin n → Ω => f (k 0) * v t)
    (funext fun i => permutationCoordinates_apply π (fun j => k j.succ) i)

/-- The full tensor-insertion adjoint preserves the actual symmetric tail subspace. -/
theorem tensorContraction_symmetric (n : ℕ) (f : Lp ℂ 2 μ)
    (u : Sector μ (n + 1)) :
    (tensorInsertion μ n f).adjoint u.val ∈ symmetricSubspace μ n := by
  intro π
  let z := (tensorInsertion μ n f).adjoint u.val
  have hi : ⟪permutation μ n π z, z⟫_ℂ = ⟪z, z⟫_ℂ := by
    calc
      _ = ⟪tensorInsertion μ n f (permutation μ n π z), u.val⟫_ℂ :=
        (tensorInsertion μ n f).adjoint_inner_right _ _
      _ = ⟪permutation μ (n + 1) (tailPermutation π) (tensorInsertion μ n f z), u.val⟫_ℂ := by
        rw [tensorInsertion_tailPermutation]
      _ = ⟪tensorInsertion μ n f z, u.val⟫_ℂ := by
        have h := (permutation μ (n + 1) (tailPermutation π)).inner_map_map
          (tensorInsertion μ n f z) u.val
        rw [u.property (tailPermutation π)] at h
        exact h
      _ = _ := ((tensorInsertion μ n f).adjoint_inner_right _ _).symm
  have hs : ‖permutation μ n π z - z‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), (permutation μ n π).norm_map, hi,
      inner_self_eq_norm_sq_to_K]
    simp only [RCLike.re_ofReal_pow]
    ring
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith only [hs, norm_nonneg (permutation μ n π z - z)]

/-- Annihilation is normalized full contraction, whose output is already symmetric. -/
theorem annihilationSector_eq_tensorContraction (n : ℕ) (f : Lp ℂ 2 μ)
    (u : Sector μ (n + 1)) :
    (annihilationSector μ n f u).val =
      (Real.sqrt (n + 1 : ℝ) : ℂ) • (tensorInsertion μ n f).adjoint u.val := by
  let z : Sector μ n := ⟨(tensorInsertion μ n f).adjoint u.val,
    tensorContraction_symmetric μ n f u⟩
  have h : annihilationSector μ n f u = (Real.sqrt (n + 1 : ℝ) : ℂ) • z := by
    apply ext_inner_left ℂ
    intro v
    calc
      _ = ⟪creationSector μ n f v, u⟫_ℂ := (annihilationSector_duality μ n f v u).symm
      _ = (Real.sqrt (n + 1 : ℝ) : ℂ) * ⟪tensorInsertion μ n f v.val, u.val⟫_ℂ := by
        change ⟪(Real.sqrt (n + 1 : ℝ) : ℂ) •
          (symmetricSubspace μ (n + 1)).orthogonalProjectionOnto
            (tensorInsertion μ n f v.val), u⟫_ℂ = _
        rw [inner_smul_left, Complex.conj_ofReal,
          Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
      _ = (Real.sqrt (n + 1 : ℝ) : ℂ) * ⟪v, z⟫_ℂ :=
        congrArg ((Real.sqrt (n + 1 : ℝ) : ℂ) * ·)
          ((tensorInsertion μ n f).adjoint_inner_right v.val u.val).symm
      _ = _ := (inner_smul_right v z (Real.sqrt (n + 1 : ℝ) : ℂ)).symm
  exact congrArg Subtype.val h

theorem annihilationSector_norm_sq_tensorContraction (n : ℕ) (f : Lp ℂ 2 μ)
    (u : Sector μ (n + 1)) :
    ‖annihilationSector μ n f u‖ ^ 2 =
      (n + 1 : ℝ) * ‖(tensorInsertion μ n f).adjoint u.val‖ ^ 2 := by
  change ‖(annihilationSector μ n f u).val‖ ^ 2 = _
  rw [annihilationSector_eq_tensorContraction, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ))]

end GptLean.PhysicalFock
