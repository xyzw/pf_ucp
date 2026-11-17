import GptLean.PhysicalWeylIntegral
import GptLean.RepresentabilityCoherent
import GptLean.WeylCoherentPhase
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-! The coherent overlap and real-subspace Lipschitz identity from the concrete
Weyl differential law and the actual zero/one particle sectors. -/

noncomputable section

namespace GptLean.Representability.ConcreteWeylLaw

open MeasureTheory PhysicalFock PhysicalWeyl
open scoped InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (W : ConcreteWeylLaw μ)

theorem inner_creationWord_of_annihilation {h : Lp ℂ 2 μ} {u v : Fock μ}
    (hv : AnnihilationGraph μ h u v) :
    ⟪creationWord μ [h], u⟫_ℂ = ⟪creationWord μ [], v⟫_ℂ := by
  change ⟪lp.single 2 1 (creationSector μ 0 h (vacuumSector μ)), u⟫_ℂ =
    ⟪lp.single 2 0 (vacuumSector μ), v⟫_ℂ
  rw [lp.inner_single_left, lp.inner_single_left, hv 0]
  exact annihilationSector_duality μ 0 h (vacuumSector μ) (u 1)

theorem vacuum_weyl_onePhoton (f h : Lp ℂ 2 μ) :
    ⟪creationWord μ [], W.weyl f (creationWord μ [h])⟫_ℂ =
      -⟪f, h⟫_ℂ * ⟪creationWord μ [], W.coherent μ f⟫_ℂ := by
  have hi (v : Fock μ) : ⟪W.coherent μ (-f), v⟫_ℂ =
      ⟪creationWord μ [], W.weyl f v⟫_ℂ := by
    simpa only [coherent, neg_neg] using inner_weyl W (-f) (creationWord μ []) v
  rw [← hi]
  have hv := inner_creationWord_of_annihilation μ (W.coherent_annihilationGraph μ (-f) h)
  have hc := congrArg (starRingEnd ℂ) hv
  simp only [map_mul, inner_smul_right, inner_neg_right, map_neg,
    inner_conj_symm] at hc
  rw [hc, hi]
  rfl

theorem vacuum_coherent_hasDerivAt (f : Lp ℂ 2 μ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪creationWord μ [], W.coherent μ (s • f)⟫_ℂ)
      (-(t * ‖f‖ ^ 2 : ℝ) * ⟪creationWord μ [], W.coherent μ (t • f)⟫_ℂ) t := by
  have hf : HasDerivAt (fun s : ℝ => s • f) f t := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id t).smul_const f
  have hcoh : HasDerivAt (fun s : ℝ => W.coherent μ (s • f))
      (W.coherentDerivative μ (t • f) f) t := by
    simpa only [phaseCoherent, phaseCoherentDerivative, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, one_smul, zero_smul, add_zero] using
      W.phaseCoherent_hasDerivAt μ (hasDerivAt_const t (0 : ℝ)) hf
  have h : HasDerivAt
      (fun s : ℝ => ⟪creationWord μ [], W.coherent μ (s • f)⟫_ℂ)
      ⟪creationWord μ [], W.coherentDerivative μ (t • f) f⟫_ℂ t :=
    ((innerSL ℂ (creationWord μ [])).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hcoh
  have htinner : ⟪t • f, f⟫_ℂ = (t : ℂ) * (‖f‖ ^ 2 : ℝ) := by
    have he : (t • f : Lp ℂ 2 μ) = (t : ℂ) • f := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_smul t f, Lp.coeFn_smul (t : ℂ) f] with x hx hy
      rw [hx, hy]
      exact (Complex.coe_smul t (f x)).symm
    rw [he, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
    simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]
  have him : (⟪t • f, f⟫_ℂ).im = 0 := by rw [htinner, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_im, mul_zero, zero_mul, add_zero]
  rw [W.coherentDerivative_apply, him] at h
  simp only [Complex.ofReal_zero, mul_zero, zero_smul, add_zero] at h
  rw [W.vacuum_weyl_onePhoton μ, htinner] at h
  exact h.congr_deriv (by push_cast; ring)

/-- Solve the scalar vacuum differential equation along a real displacement ray. -/
theorem vacuum_coherent_inner_ray (f : Lp ℂ 2 μ) (t : ℝ) :
    ⟪creationWord μ [], W.coherent μ (t • f)⟫_ℂ =
      Complex.exp ((-(t ^ 2 * ‖f‖ ^ 2 / 2) : ℝ) : ℂ) := by
  let v := fun s : ℝ => ⟪creationWord μ [], W.coherent μ (s • f)⟫_ℂ
  let q := fun s : ℝ => Complex.exp (((s ^ 2 * ‖f‖ ^ 2 / 2 : ℝ) : ℂ)) * v s
  have hq (s : ℝ) : HasDerivAt q 0 s := by
    have hg : HasDerivAt (fun r : ℝ => ((r ^ 2 * ‖f‖ ^ 2 / 2 : ℝ) : ℂ))
        ((s * ‖f‖ ^ 2 : ℝ) : ℂ) s := by
      have hr : HasDerivAt (fun r : ℝ => r ^ 2 * ‖f‖ ^ 2 / 2)
          (s * ‖f‖ ^ 2) s := by
        apply ((((hasDerivAt_id s).pow 2).mul_const (‖f‖ ^ 2)).div_const 2).congr_deriv
        norm_num
        ring
      exact hr.ofReal_comp
    have hv := W.vacuum_coherent_hasDerivAt μ f s
    have hprod := hg.cexp.mul hv
    exact hprod.congr_deriv (by push_cast; ring)
  have he := is_const_of_deriv_eq_zero (fun s => (hq s).differentiableAt)
    (fun s => (hq s).deriv) t 0
  have hzero : q 0 = 1 := by
    simp only [q, v, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_div,
      Complex.ofReal_zero, Complex.exp_zero, one_mul, zero_smul, coherent, W.zero,
      LinearIsometryEquiv.coe_refl, id_eq, inner_self_eq_norm_sq_to_K, vacuum_norm,
      RCLike.ofReal_one, one_pow]
  have hval : Complex.exp (((t ^ 2 * ‖f‖ ^ 2 / 2 : ℝ) : ℂ)) * v t = 1 :=
    he.trans hzero
  change v t = _
  calc
    v t = Complex.exp ((-(t ^ 2 * ‖f‖ ^ 2 / 2) : ℝ) : ℂ) *
        (Complex.exp (((t ^ 2 * ‖f‖ ^ 2 / 2 : ℝ) : ℂ)) * v t) := by
      rw [← mul_assoc, ← Complex.exp_add]
      simp
    _ = _ := by rw [hval, mul_one]

theorem vacuum_coherent_inner (f : Lp ℂ 2 μ) :
    ⟪creationWord μ [], W.coherent μ f⟫_ℂ =
      Complex.exp ((-(‖f‖ ^ 2 / 2) : ℝ) : ℂ) := by
  simpa only [one_smul, one_pow, one_mul] using W.vacuum_coherent_inner_ray μ f 1

/-- The full coherent overlap, including its symplectic phase. -/
theorem coherent_inner (f g : Lp ℂ 2 μ) :
    ⟪W.coherent μ f, W.coherent μ g⟫_ℂ =
      Complex.exp (((-(‖f - g‖ ^ 2 / 2) : ℝ) : ℂ) +
        Complex.I * ((⟪f, g⟫_ℂ).im : ℂ)) := by
  change ⟪W.weyl f (creationWord μ []), W.weyl g (creationWord μ [])⟫_ℂ = _
  rw [inner_weyl, W.compose, inner_smul_right]
  change Complex.exp (-Complex.I * ((⟪-f, g⟫_ℂ).im : ℂ)) *
    ⟪creationWord μ [], W.coherent μ (-f + g)⟫_ℂ = _
  rw [W.vacuum_coherent_inner μ, ← Complex.exp_add]
  congr 1
  have hn : ‖-f + g‖ = ‖f - g‖ := by rw [neg_add_eq_sub, norm_sub_rev]
  rw [hn, inner_neg_left, Complex.neg_im]
  push_cast
  ring

/-- The exact distance formula on every real subspace with vanishing symplectic pairing. -/
theorem coherent_dist_sq_of_real (f g : Lp ℂ 2 μ) (hreal : (⟪f, g⟫_ℂ).im = 0) :
    ‖W.coherent μ f - W.coherent μ g‖ ^ 2 =
      2 * (1 - Real.exp (-(‖f - g‖ ^ 2 / 2))) := by
  rw [norm_sub_sq (𝕜 := ℂ), W.coherent_norm μ, W.coherent_norm μ, W.coherent_inner μ, hreal]
  simp only [Complex.ofReal_zero, mul_zero, add_zero, RCLike.re_to_complex, Complex.exp_ofReal_re]
  ring

theorem coherent_dist_le_of_real (f g : Lp ℂ 2 μ) (hreal : (⟪f, g⟫_ℂ).im = 0) :
    ‖W.coherent μ f - W.coherent μ g‖ ≤ ‖f - g‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [W.coherent_dist_sq_of_real μ f g hreal]
  have h := Real.add_one_le_exp (-(‖f - g‖ ^ 2 / 2))
  linarith

end GptLean.Representability.ConcreteWeylLaw
