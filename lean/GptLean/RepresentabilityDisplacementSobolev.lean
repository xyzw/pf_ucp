import GptLean.RepresentabilityDisplacement
import GptLean.Repair.MeasuredTagSobolev

/-!
The weighted L2 displacement has a representative on the whole position
space with local weak H1 regularity. This construction never differentiates
the density. Bounded first derivatives of the coupling family and the weak
derivatives of the prescribed profile give weighted square-integrable
derivatives of the displacement, even when the density vanishes.
-/

noncomputable section
set_option Elab.async false

namespace GptLean.Representability

open MeasureTheory SymmetricLift Repair
open scoped ENNReal InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

abbrev DisplacementPosition := EuclideanSpace ℝ (Fin 3)

def adjointEvaluation (q : H) : (V →L[ℝ] H) →L[ℝ] V where
  toFun A := A.adjoint q
  map_add' A B := by simp
  map_smul' c A := by simp
  cont := ContinuousLinearMap.adjoint.continuous.clm_apply continuous_const

@[simp] theorem adjointEvaluation_apply (q : H) (A : V →L[ℝ] H) :
    adjointEvaluation q A = A.adjoint q := rfl

variable {μ : Measure DisplacementPosition} [IsFiniteMeasure μ]
  (G : BoundedCoupling μ V H)

/-- A uniform bound on a coupling derivative gives its weighted L2 bound. -/
theorem coupling_derivative_memLp
    (dG : Fin 3 → DisplacementPosition → V →L[ℝ] H)
    (hdG : ∀ i, AEStronglyMeasurable (dG i) μ)
    (L : ℝ) (hL : ∀ i x, ‖dG i x‖ ≤ L) (q : H) (i : Fin 3) :
    MemLp (fun x => (dG i x).adjoint q) 2 μ := by
  apply MemLp.of_bound ((adjointEvaluation q).continuous.comp_aestronglyMeasurable (hdG i))
    (L * ‖q‖)
  exact ae_of_all _ fun x => ((dG i x).adjoint.le_opNorm q).trans
    (mul_le_mul_of_nonneg_right (by simpa using hL i x) (norm_nonneg _))

omit [IsFiniteMeasure μ] in
/-- Ordinary bounded differentiability of the coupling family gives the
local weak derivative of every kernel profile. -/
theorem coupling_profile_weakH1
    (dG : Fin 3 → DisplacementPosition → V →L[ℝ] H)
    (hG : Continuous G.value)
    (hd : ∀ i x, HasLineDerivAt ℝ G.value (dG i x) x (EuclideanSpace.single i 1))
    (L : ℝ) (hL : ∀ i x, ‖dG i x‖ ≤ L) (q : H) :
    HasWeakH1Local (fun x => (G.value x).adjoint q)
      (fun i x => (dG i x).adjoint q) := by
  apply weakH1Local_of_continuous_bounded_lineDeriv
    ((adjointEvaluation q).continuous.comp hG)
    (fun i x => (adjointEvaluation q).hasFDerivAt.comp_hasDerivAt 0 (hd i x))
    (L * ‖q‖)
  intro i x
  exact ((dG i x).adjoint.le_opNorm q).trans
    (mul_le_mul_of_nonneg_right (by simpa using hL i x) (norm_nonneg _))

/-- A representative defined on all of space, with the prescribed weak
regularity and finite weighted derivative norms. The field equation holds
with respect to the density measure, while local H1 uses ordinary volume. -/
theorem displacement_weakH1_formula_exists
    (dG : Fin 3 → DisplacementPosition → V →L[ℝ] H)
    (hG : Continuous G.value)
    (hd : ∀ i x, HasLineDerivAt ℝ G.value (dG i x) x (EuclideanSpace.single i 1))
    (hdG : ∀ i, AEStronglyMeasurable (dG i) μ)
    (L : ℝ) (hL : ∀ i x, ‖dG i x‖ ≤ L)
    (M : V →L[ℝ] V) (N : ℕ) (hN : 1 ≤ N)
    (ell : ℝ) (hell : 0 < ell)
    (hM : ∀ v, ell * ‖v‖ ^ 2 ≤ ⟪v, M v⟫_ℝ)
    (a : DisplacementPosition → V) (da : Fin 3 → DisplacementPosition → V)
    (ha : HasWeakH1Local a da) (haμ : MemLp a 2 μ)
    (hdaμ : ∀ i, MemLp (da i) 2 μ) :
    ∃ (u : DisplacementPosition → V) (du : Fin 3 → DisplacementPosition → V),
      HasWeakH1Local u du ∧ MemLp u 2 μ ∧ (∀ i, MemLp (du i) 2 μ) ∧
      (eLpNorm u 2 μ).toReal ≤ ell⁻¹ * (eLpNorm a 2 μ).toReal ∧
      (∀ᵐ x ∂μ, M (u x) + (((N : ℝ) - 1) / (N : ℝ)) •
        ((2 : ℝ) • ((G.value x).adjoint (∫ y, G.value y (u y) ∂μ))) = a x) ∧
      (∀ i x, du i x = (coerciveFieldEquiv M ell hell hM).symm
        (da i x + (-(((N : ℝ) - 1) / (N : ℝ)) * 2) •
          ((dG i x).adjoint (∫ y, G.value y (u y) ∂μ)))) := by
  let α : ℝ := ((N : ℝ) - 1) / (N : ℝ)
  obtain ⟨u₀, heq, hnorm, _⟩ := G.displacement_exists M N hN ell hell hM (haμ.toLp a)
  let q := G.analysis.adjoint u₀
  let B := (coerciveFieldEquiv M ell hell hM).symm.toContinuousLinearMap
  let u := fun x => B (a x + (-α * 2) • ((G.value x).adjoint q))
  let du := fun i x => B (da i x + (-α * 2) • ((dG i x).adjoint q))
  have huweak : HasWeakH1Local u du := by
    exact weakH1Local_map B (weakH1Local_add ha
      (weakH1Local_map ((-α * 2) • ContinuousLinearMap.id ℝ V)
        (coupling_profile_weakH1 G dG hG hd L hL q)))
  have huμ : MemLp u 2 μ :=
    B.comp_memLp' (haμ.add ((G.adjoint_memLp q).const_smul (-α * 2)))
  have hduμ : ∀ i, MemLp (du i) 2 μ := fun i =>
    B.comp_memLp' ((hdaμ i).add
      ((coupling_derivative_memLp dG hdG L hL q i).const_smul (-α * 2)))
  have hu_eq : u =ᵐ[μ] (u₀ : DisplacementPosition → V) := by
    have hp : (M.compLpL 2 μ u₀ + α • G.kernel u₀ : Lp V 2 μ)
        =ᵐ[μ] (haμ.toLp a : DisplacementPosition → V) := by rw [heq]
    filter_upwards [hp, haμ.coeFn_toLp,
      Lp.coeFn_add (M.compLpL 2 μ u₀) (α • G.kernel u₀),
      Lp.coeFn_smul α (G.kernel u₀), M.coeFn_compLpL u₀, G.kernel_ae u₀]
      with x hx ha hadd hsmul hmap hk
    simp only [hadd, Pi.add_apply, hsmul, Pi.smul_apply, hmap, hk, ha,
      ← G.synthesis_eq_integral] at hx
    change M (u₀ x) + α • ((2 : ℝ) • ((G.value x).adjoint q)) = a x at hx
    have hr : a x + (-α * 2) • ((G.value x).adjoint q) = M (u₀ x) := by
      rw [← hx, ← smul_smul]
      simp only [neg_smul]
      abel
    change B (a x + (-α * 2) • ((G.value x).adjoint q)) = u₀ x
    rw [hr]
    simpa only [B, ContinuousLinearEquiv.coe_coe, coerciveFieldEquiv_apply] using!
      (coerciveFieldEquiv M ell hell hM).symm_apply_apply (u₀ x)
  have hq : (∫ y, G.value y (u y) ∂μ) = q := by
    rw [show q = ∫ y, G.value y (u₀ y) ∂μ from G.synthesis_eq_integral u₀]
    exact integral_congr_ae (hu_eq.mono fun x hx => congrArg (G.value x) hx)
  have hunorm : (eLpNorm u 2 μ).toReal ≤ ell⁻¹ * (eLpNorm a 2 μ).toReal := by
    rw [eLpNorm_congr_ae hu_eq, ← Lp.norm_def, ← Lp.norm_toLp a haμ]
    exact hnorm
  refine ⟨u, du, huweak, huμ, hduμ, hunorm, ?_, ?_⟩
  swap
  · intro i x
    rw [hq]
    rfl
  have hMu (x) : M (u x) = a x + (-α * 2) • ((G.value x).adjoint q) := by
    simpa only [u, B, ContinuousLinearEquiv.coe_coe, coerciveFieldEquiv_apply] using!
      (coerciveFieldEquiv M ell hell hM).apply_symm_apply
        (a x + (-α * 2) • ((G.value x).adjoint q))
  exact ae_of_all _ fun x => by
    rw [hq, hMu]
    change a x + (-α * 2) • _ + α • ((2 : ℝ) • _) = a x
    rw [← smul_smul, neg_smul]
    abel

/-- The weighted weak solution, with the derivative formula suppressed. -/
theorem displacement_weakH1_exists
    (dG : Fin 3 → DisplacementPosition → V →L[ℝ] H)
    (hG : Continuous G.value)
    (hd : ∀ i x, HasLineDerivAt ℝ G.value (dG i x) x (EuclideanSpace.single i 1))
    (hdG : ∀ i, AEStronglyMeasurable (dG i) μ)
    (L : ℝ) (hL : ∀ i x, ‖dG i x‖ ≤ L)
    (M : V →L[ℝ] V) (N : ℕ) (hN : 1 ≤ N)
    (ell : ℝ) (hell : 0 < ell)
    (hM : ∀ v, ell * ‖v‖ ^ 2 ≤ ⟪v, M v⟫_ℝ)
    (a : DisplacementPosition → V) (da : Fin 3 → DisplacementPosition → V)
    (ha : HasWeakH1Local a da) (haμ : MemLp a 2 μ)
    (hdaμ : ∀ i, MemLp (da i) 2 μ) :
    ∃ (u : DisplacementPosition → V) (du : Fin 3 → DisplacementPosition → V),
      HasWeakH1Local u du ∧ MemLp u 2 μ ∧ (∀ i, MemLp (du i) 2 μ) ∧
      (eLpNorm u 2 μ).toReal ≤ ell⁻¹ * (eLpNorm a 2 μ).toReal ∧
      (∀ᵐ x ∂μ, M (u x) + (((N : ℝ) - 1) / (N : ℝ)) •
        ((2 : ℝ) • ((G.value x).adjoint (∫ y, G.value y (u y) ∂μ))) = a x) := by
  obtain ⟨u, du, hw, hu, hdu, hn, he, _⟩ :=
    displacement_weakH1_formula_exists G dG hG hd hdG L hL M N hN ell hell hM
      a da ha haμ hdaμ
  exact ⟨u, du, hw, hu, hdu, hn, he⟩

end GptLean.Representability
