import GptLean.Repair.ParameterSections

/-! Exact L2 multiplication terms in a quadratic form.

These generic Hilbert-fibre identities isolate the integration and norm
algebra used by the physical shifted-energy bridge.
-/

noncomputable section
namespace PfHk.PhysicalShiftedFormEnergyLp

open MeasureTheory GptLean
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 40000

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem real_smul_norm_sq (a : ℝ) (v : H) :
    ‖a • v‖ ^ 2 = a ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem sqrt_smul_norm_sq (a : ℝ) (ha : 0 ≤ a) (v : H) :
    ‖(Real.sqrt a : ℂ) • v‖ ^ 2 = a * ‖v‖ ^ 2 := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ha]

theorem multiplier_square_integrable (u : Lp H 2 μ) (a : X → ℝ)
    (ha : MemLp (fun x => a x • u x) 2 μ) :
    Integrable (fun x => a x ^ 2 * ‖u x‖ ^ 2) μ :=
  ha.norm.integrable_sq.congr (Filter.Eventually.of_forall fun x =>
    real_smul_norm_sq (a x) (u x))

theorem multiplier_norm_sq (u : Lp H 2 μ) (a : X → ℝ)
    (ha : MemLp (fun x => a x • u x) 2 μ) :
    ‖ha.toLp (fun x => a x • u x)‖ ^ 2 = ∫ x, a x ^ 2 * ‖u x‖ ^ 2 ∂μ :=
  (Repair.toL2_norm_sq ha).trans (integral_congr_ae
    (Filter.Eventually.of_forall fun x => real_smul_norm_sq (a x) (u x)))

private theorem real_inner_smul_left (a : ℝ) (u v : H) :
    (⟪a • u, v⟫_ℂ).re = a * (⟪u, v⟫_ℂ).re := by
  rw [inner_smul_left_eq_smul, Complex.smul_re, smul_eq_mul]

theorem multiplier_cross_integrable (u v : Lp H 2 μ) (a : X → ℝ)
    (ha : MemLp (fun x => a x • u x) 2 μ) :
    Integrable (fun x => a x * (⟪u x, v x⟫_ℂ).re) μ := by
  have he : (fun x => (⟪ha.toLp (fun x => a x • u x) x, v x⟫_ℂ).re) =ᵐ[μ]
      fun x => a x * (⟪u x, v x⟫_ℂ).re := by
    filter_upwards [ha.coeFn_toLp] with x hx
    exact (congrArg (fun w : H => (⟪w, v x⟫_ℂ).re) hx).trans
      (real_inner_smul_left (a x) (u x) (v x))
  exact (L2.integrable_inner (𝕜 := ℂ) (ha.toLp _) v).re.congr he

theorem multiplier_inner_re (u v : Lp H 2 μ) (a : X → ℝ)
    (ha : MemLp (fun x => a x • u x) 2 μ) :
    (⟪ha.toLp (fun x => a x • u x), v⟫_ℂ).re =
      ∫ x, a x * (⟪u x, v x⟫_ℂ).re ∂μ := by
  have he : (fun x => (⟪ha.toLp (fun x => a x • u x) x, v x⟫_ℂ).re) =ᵐ[μ]
      fun x => a x * (⟪u x, v x⟫_ℂ).re := by
    filter_upwards [ha.coeFn_toLp] with x hx
    exact (congrArg (fun w : H => (⟪w, v x⟫_ℂ).re) hx).trans
      (real_inner_smul_left (a x) (u x) (v x))
  exact (congrArg Complex.re (L2.inner_def (ha.toLp _) v)).trans
    ((integral_re (L2.integrable_inner (𝕜 := ℂ) (ha.toLp _) v)).symm.trans
      (integral_congr_ae he))

theorem norm_add_multiplier_sq (u v : Lp H 2 μ) (a : X → ℝ)
    (ha : MemLp (fun x => a x • u x) 2 μ) :
    ‖v + ha.toLp (fun x => a x • u x)‖ ^ 2 = ‖v‖ ^ 2 +
      2 * (∫ x, a x * (⟪u x, v x⟫_ℂ).re ∂μ) +
      ∫ x, a x ^ 2 * ‖u x‖ ^ 2 ∂μ := by
  have hc : (⟪v, ha.toLp (fun x => a x • u x)⟫_ℂ).re =
      (⟪ha.toLp (fun x => a x • u x), v⟫_ℂ).re := by
    have h := congrArg Complex.re (inner_conj_symm v (ha.toLp _))
    simpa only [Complex.conj_re] using h.symm
  have hn := norm_add_sq (𝕜 := ℂ) v (ha.toLp (fun x => a x • u x))
  change ‖v + ha.toLp (fun x => a x • u x)‖ ^ 2 = ‖v‖ ^ 2 +
    2 * (⟪v, ha.toLp (fun x => a x • u x)⟫_ℂ).re + ‖ha.toLp _‖ ^ 2 at hn
  exact hn.trans (congrArg₂ (· + ·)
    (congrArg (fun r : ℝ => ‖v‖ ^ 2 + 2 * r)
      (hc.trans (multiplier_inner_re u v a ha)))
    (multiplier_norm_sq u a ha))

theorem signed_multiplier_difference (u : Lp H 2 μ) (p n w : X → ℝ)
    (hp : MemLp (fun x => p x • u x) 2 μ)
    (hn : MemLp (fun x => n x • u x) 2 μ)
    (hw : ∀ᵐ x ∂μ, p x ^ 2 - n x ^ 2 = w x) :
    ‖hp.toLp (fun x => p x • u x)‖ ^ 2 -
      ‖hn.toLp (fun x => n x • u x)‖ ^ 2 = ∫ x, w x * ‖u x‖ ^ 2 ∂μ := by
  have he : (fun x => p x ^ 2 * ‖u x‖ ^ 2 - n x ^ 2 * ‖u x‖ ^ 2) =ᵐ[μ]
      fun x => w x * ‖u x‖ ^ 2 :=
    hw.mono fun x hx => (sub_mul _ _ _).symm.trans (congrArg (· * ‖u x‖ ^ 2) hx)
  exact (congrArg₂ (· - ·) (multiplier_norm_sq u p hp) (multiplier_norm_sq u n hn)).trans
    ((integral_sub (multiplier_square_integrable u p hp)
      (multiplier_square_integrable u n hn)).symm.trans (integral_congr_ae he))

end PfHk.PhysicalShiftedFormEnergyLp
