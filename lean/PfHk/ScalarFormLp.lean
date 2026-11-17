import GptLean.Repair.ParameterSections

/-! Real parts of scalar multiplier forms in L2. -/

noncomputable section
namespace PfHk.ScalarFormLp

open MeasureTheory
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 40000

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem inner_real_smul_both (a : ℝ) (u v : H) :
    (⟪a • u, a • v⟫_ℂ).re = a ^ 2 * (⟪u, v⟫_ℂ).re := by
  simp only [inner_smul_left_eq_smul, inner_smul_right_eq_smul,
    Complex.smul_re, smul_eq_mul]
  ring

theorem pair_integrable (u v pu pv : Lp H 2 μ) (p : X → ℝ)
    (hu : pu =ᵐ[μ] fun x => p x • u x)
    (hv : pv =ᵐ[μ] fun x => p x • v x) :
    Integrable (fun x => p x ^ 2 * (⟪u x, v x⟫_ℂ).re) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) pu pv).re.congr
  filter_upwards [hu, hv] with x hux hvx
  exact (congrArg₂ (fun a b : H => (⟪a, b⟫_ℂ).re) hux hvx).trans
    (inner_real_smul_both (p x) (u x) (v x))

theorem pair_re (u v pu pv : Lp H 2 μ) (p : X → ℝ)
    (hu : pu =ᵐ[μ] fun x => p x • u x)
    (hv : pv =ᵐ[μ] fun x => p x • v x) :
    (⟪pu, pv⟫_ℂ).re = ∫ x, p x ^ 2 * (⟪u x, v x⟫_ℂ).re ∂μ := by
  refine (congrArg Complex.re (L2.inner_def pu pv)).trans
    ((integral_re (L2.integrable_inner (𝕜 := ℂ) pu pv)).symm.trans ?_)
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hux hvx
  exact (congrArg₂ (fun a b : H => (⟪a, b⟫_ℂ).re) hux hvx).trans
    (inner_real_smul_both (p x) (u x) (v x))

theorem signed_pair_integrable (u v pu pv nu nv : Lp H 2 μ) (p n w : X → ℝ)
    (hpu : pu =ᵐ[μ] fun x => p x • u x)
    (hpv : pv =ᵐ[μ] fun x => p x • v x)
    (hnu : nu =ᵐ[μ] fun x => n x • u x)
    (hnv : nv =ᵐ[μ] fun x => n x • v x)
    (hw : ∀ᵐ x ∂μ, p x ^ 2 - n x ^ 2 = w x) :
    Integrable (fun x => w x * (⟪u x, v x⟫_ℂ).re) μ := by
  apply ((pair_integrable u v pu pv p hpu hpv).sub
    (pair_integrable u v nu nv n hnu hnv)).congr
  filter_upwards [hw] with x hx
  exact (sub_mul _ _ _).symm.trans (congrArg (· * (⟪u x, v x⟫_ℂ).re) hx)

theorem signed_pair_re (u v pu pv nu nv : Lp H 2 μ) (p n w : X → ℝ)
    (hpu : pu =ᵐ[μ] fun x => p x • u x)
    (hpv : pv =ᵐ[μ] fun x => p x • v x)
    (hnu : nu =ᵐ[μ] fun x => n x • u x)
    (hnv : nv =ᵐ[μ] fun x => n x • v x)
    (hw : ∀ᵐ x ∂μ, p x ^ 2 - n x ^ 2 = w x) :
    (⟪pu, pv⟫_ℂ).re - (⟪nu, nv⟫_ℂ).re =
      ∫ x, w x * (⟪u x, v x⟫_ℂ).re ∂μ := by
  refine (congrArg₂ (· - ·) (pair_re u v pu pv p hpu hpv)
    (pair_re u v nu nv n hnu hnv)).trans
    ((integral_sub (pair_integrable u v pu pv p hpu hpv)
      (pair_integrable u v nu nv n hnu hnv)).symm.trans ?_)
  apply integral_congr_ae
  filter_upwards [hw] with x hx
  exact (sub_mul _ _ _).symm.trans (congrArg (· * (⟪u x, v x⟫_ℂ).re) hx)

end PfHk.ScalarFormLp
