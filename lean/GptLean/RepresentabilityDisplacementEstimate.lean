import GptLean.RepresentabilityDisplacementSobolev

/-!
Quantitative estimates for the weighted displacement construction. The
coupling bounds depend on the total mass of the measure, rather than its
spatial distribution. This is the input needed for a density-independent
constant in the final kinetic estimate.
-/

noncomputable section
set_option Elab.async false

namespace GptLean.Representability

open MeasureTheory SymmetricLift
open scoped ENNReal InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem coerciveFieldEquiv_symm_bound (M : V →L[ℝ] V)
    (ell : ℝ) (hell : 0 < ell)
    (hM : ∀ v, ell * ‖v‖ ^ 2 ≤ ⟪v, M v⟫_ℝ) (v : V) :
    ‖(coerciveFieldEquiv M ell hell hM).symm v‖ ≤ ell⁻¹ * ‖v‖ := by
  apply displacement_solution_bound M ell hell hM _ v
  simpa only [coerciveFieldEquiv_apply] using
    (coerciveFieldEquiv M ell hell hM).apply_symm_apply v

theorem coerciveFieldEquiv_symm_norm_le (M : V →L[ℝ] V)
    (ell : ℝ) (hell : 0 < ell)
    (hM : ∀ v, ell * ‖v‖ ^ 2 ≤ ⟪v, M v⟫_ℝ) :
    ‖(coerciveFieldEquiv M ell hell hM).symm.toContinuousLinearMap‖ ≤ ell⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hell.le)
  exact coerciveFieldEquiv_symm_bound M ell hell hM

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

namespace BoundedCoupling

theorem analysis_norm_le (G : BoundedCoupling μ V H) :
    ‖G.analysis‖ ≤ (measureUnivNNReal μ : ℝ) ^ (1 / 2 : ℝ) * G.bound := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _) G.bound_nonneg)
  exact G.analysisLinear_bound

theorem synthesis_norm_le (G : BoundedCoupling μ V H) (u : Lp V 2 μ) :
    ‖∫ x, G.value x (u x) ∂μ‖ ≤
      ((measureUnivNNReal μ : ℝ) ^ (1 / 2 : ℝ) * G.bound) * ‖u‖ := by
  rw [← G.synthesis_eq_integral]
  exact (G.analysis.adjoint.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (by simpa using G.analysis_norm_le) (norm_nonneg u))

end BoundedCoupling

omit [IsFiniteMeasure μ] in
theorem coercive_map_l2_bound (M : V →L[ℝ] V)
    (ell : ℝ) (hell : 0 < ell)
    (hM : ∀ v, ell * ‖v‖ ^ 2 ≤ ⟪v, M v⟫_ℝ)
    (f : X → V) (hf : MemLp f 2 μ) :
    (eLpNorm (fun x => (coerciveFieldEquiv M ell hell hM).symm (f x)) 2 μ).toReal ≤
      ell⁻¹ * (eLpNorm f 2 μ).toReal := by
  let B := (coerciveFieldEquiv M ell hell hM).symm.toContinuousLinearMap
  have he : (B.compLpL 2 μ (hf.toLp f) : X → V) =ᵐ[μ] fun x => B (f x) :=
    (B.coeFn_compLpL (hf.toLp f)).trans (hf.coeFn_toLp.fun_comp B)
  change (eLpNorm (fun x => B (f x)) 2 μ).toReal ≤ _
  rw [← eLpNorm_congr_ae he, ← Lp.norm_def, ← Lp.norm_toLp f hf]
  exact ((B.compLpL 2 μ).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right
      (B.norm_compLpL_le.trans (coerciveFieldEquiv_symm_norm_le M ell hell hM))
      (norm_nonneg _))

omit [IsFiniteMeasure μ] [CompleteSpace V] in
theorem l2_add_smul_bound (f g : X → V) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (c : ℝ) :
    (eLpNorm (fun x => f x + c • g x) 2 μ).toReal ≤
      (eLpNorm f 2 μ).toReal + |c| * (eLpNorm g 2 μ).toReal := by
  change (eLpNorm (f + c • g) 2 μ).toReal ≤ _
  rw [← Lp.norm_toLp (f + c • g) (hf.add (hg.const_smul c)),
    MemLp.toLp_add hf (hg.const_smul c), MemLp.toLp_const_smul c hg]
  simpa only [norm_smul, Real.norm_eq_abs, Lp.norm_toLp] using
    norm_add_le (hf.toLp f) (c • hg.toLp g)

theorem coupling_derivative_l2_bound
    {μ : Measure DisplacementPosition} [IsFiniteMeasure μ]
    (dG : Fin 3 → DisplacementPosition → V →L[ℝ] H)
    (hdG : ∀ i, AEStronglyMeasurable (dG i) μ)
    (L : ℝ) (hL0 : 0 ≤ L) (hL : ∀ i x, ‖dG i x‖ ≤ L) (q : H) (i : Fin 3) :
    (eLpNorm (fun x => (dG i x).adjoint q) 2 μ).toReal ≤
      (measureUnivNNReal μ : ℝ) ^ (1 / 2 : ℝ) * (L * ‖q‖) := by
  let hf := coupling_derivative_memLp dG hdG L hL q i
  rw [← Lp.norm_toLp _ hf]
  have hb : ∀ᵐ x ∂μ, ‖hf.toLp _ x‖ ≤ L * ‖q‖ := by
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
    exact ((dG i x).adjoint.le_opNorm q).trans
      (mul_le_mul_of_nonneg_right (by simpa using hL i x) (norm_nonneg _))
  convert Lp.norm_le_of_ae_bound (mul_nonneg hL0 (norm_nonneg q)) hb using 1
  norm_num

/-- This coefficient sees a measure only through its total mass. -/
def displacementDerivativeConstant (mass Gbound L ell : ℝ) (N : ℕ) : ℝ :=
  ell⁻¹ * (|(-(((N : ℝ) - 1) / (N : ℝ)) * 2)| *
    (mass ^ (1 / 2 : ℝ) *
      (L * ((mass ^ (1 / 2 : ℝ) * Gbound) * ell⁻¹))))

theorem displacementDerivativeConstant_nonneg
    (mass Gbound L ell : ℝ) (N : ℕ)
    (hmass : 0 ≤ mass) (hG : 0 ≤ Gbound) (hL : 0 ≤ L) (hell : 0 < ell) :
    0 ≤ displacementDerivativeConstant mass Gbound L ell N := by
  unfold displacementDerivativeConstant
  positivity

/-- The actual weighted weak inverse has a quantitative derivative bound.
Its constants use only coercivity, coupling bounds and total measure mass. -/
theorem displacement_weakH1_estimate_exists
    {μ : Measure DisplacementPosition} [IsFiniteMeasure μ]
    (G : BoundedCoupling μ V H)
    (dG : Fin 3 → DisplacementPosition → V →L[ℝ] H)
    (hG : Continuous G.value)
    (hd : ∀ i x, HasLineDerivAt ℝ G.value (dG i x) x (EuclideanSpace.single i 1))
    (hdG : ∀ i, AEStronglyMeasurable (dG i) μ)
    (L : ℝ) (hL0 : 0 ≤ L) (hL : ∀ i x, ‖dG i x‖ ≤ L)
    (M : V →L[ℝ] V) (N : ℕ) (hN : 1 ≤ N)
    (ell : ℝ) (hell : 0 < ell)
    (hM : ∀ v, ell * ‖v‖ ^ 2 ≤ ⟪v, M v⟫_ℝ)
    (a : DisplacementPosition → V) (da : Fin 3 → DisplacementPosition → V)
    (ha : HasWeakH1Local a da) (haμ : MemLp a 2 μ)
    (hdaμ : ∀ i, MemLp (da i) 2 μ) :
    ∃ (u : DisplacementPosition → V) (du : Fin 3 → DisplacementPosition → V),
      HasWeakH1Local u du ∧ MemLp u 2 μ ∧ (∀ i, MemLp (du i) 2 μ) ∧
      (eLpNorm u 2 μ).toReal ≤ ell⁻¹ * (eLpNorm a 2 μ).toReal ∧
      (∀ i, (eLpNorm (du i) 2 μ).toReal ≤
        ell⁻¹ * (eLpNorm (da i) 2 μ).toReal +
          displacementDerivativeConstant (measureUnivNNReal μ) G.bound L ell N *
            (eLpNorm a 2 μ).toReal) ∧
      (∀ᵐ x ∂μ, M (u x) + (((N : ℝ) - 1) / (N : ℝ)) •
        ((2 : ℝ) • ((G.value x).adjoint (∫ y, G.value y (u y) ∂μ))) = a x) := by
  obtain ⟨u, du, hw, hu, hdu, hn, he, hdformula⟩ :=
    displacement_weakH1_formula_exists G dG hG hd hdG L hL M N hN ell hell hM
      a da ha haμ hdaμ
  refine ⟨u, du, hw, hu, hdu, hn, ?_, he⟩
  let q : H := ∫ y, G.value y (u y) ∂μ
  let c : ℝ := -(((N : ℝ) - 1) / (N : ℝ)) * 2
  let m : ℝ := (measureUnivNNReal μ : ℝ) ^ (1 / 2 : ℝ)
  have hm : 0 ≤ m := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hq : ‖q‖ ≤ (m * G.bound) *
      (ell⁻¹ * (eLpNorm a 2 μ).toReal) := by
    have hqi : q = ∫ y, G.value y (hu.toLp u y) ∂μ := by
      exact integral_congr_ae (hu.coeFn_toLp.symm.mono fun x hx => congrArg (G.value x) hx)
    rw [hqi]
    exact (G.synthesis_norm_le (hu.toLp u)).trans
      (mul_le_mul_of_nonneg_left (by simpa only [Lp.norm_toLp] using hn)
        (mul_nonneg hm G.bound_nonneg))
  intro i
  let g : DisplacementPosition → V := fun x => (dG i x).adjoint q
  have hg : MemLp g 2 μ := coupling_derivative_memLp dG hdG L hL q i
  have hg_bound : (eLpNorm g 2 μ).toReal ≤
      m * (L * ((m * G.bound) * (ell⁻¹ * (eLpNorm a 2 μ).toReal))) := by
    exact (coupling_derivative_l2_bound dG hdG L hL0 hL q i).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hL0) hm)
  have hf : MemLp (fun x => da i x + c • g x) 2 μ := (hdaμ i).add (hg.const_smul c)
  have hid : du i = fun x => (coerciveFieldEquiv M ell hell hM).symm
      (da i x + c • g x) := funext (hdformula i)
  rw [hid]
  calc
    _ ≤ ell⁻¹ * (eLpNorm (fun x => da i x + c • g x) 2 μ).toReal :=
      coercive_map_l2_bound M ell hell hM _ hf
    _ ≤ ell⁻¹ * ((eLpNorm (da i) 2 μ).toReal + |c| * (eLpNorm g 2 μ).toReal) :=
      mul_le_mul_of_nonneg_left (l2_add_smul_bound (da i) g (hdaμ i) hg c)
        (inv_nonneg.mpr hell.le)
    _ ≤ ell⁻¹ * ((eLpNorm (da i) 2 μ).toReal + |c| *
        (m * (L * ((m * G.bound) * (ell⁻¹ * (eLpNorm a 2 μ).toReal))))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hg_bound (abs_nonneg c)))
        (inv_nonneg.mpr hell.le)
    _ = _ := by dsimp [displacementDerivativeConstant, c, m]; ring

end GptLean.Representability
