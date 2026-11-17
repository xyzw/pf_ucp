import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-! Complex Euler--Lagrange equations on a linear sector.

A normalized minimizer of a Hermitian quadratic form satisfies its weak
eigenvalue equation against every vector in the sector. The homogeneous
Rayleigh bound and both real variations are proved here. No stationarity
or eigenvalue equation is an input.
-/

noncomputable section
namespace PfHk.FermionicVariational

open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 40000

private theorem linear_zero {a b : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t * a + t ^ 2 * b) : a = 0 := by
  by_contra ha
  let t : ℝ := -a / (2 * (|b| + 1))
  have hden : 0 < 2 * (|b| + 1) := by positivity
  have hta : t * (2 * (|b| + 1)) = -a := div_mul_cancel₀ _ hden.ne'
  have ht : t ≠ 0 := div_ne_zero (neg_ne_zero.mpr ha) hden.ne'
  have hquad := h t
  have hsq : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have hb : b ≤ |b| := le_abs_self b
  have hmul := congrArg (fun r : ℝ => t * r) hta
  nlinarith only [hmul, hquad, hsq,
    mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hb),
    mul_nonneg (sq_nonneg t) (abs_nonneg b)]

variable {Q H : Type*} [AddCommGroup Q] [Module ℂ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem form_real_smul (q : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ)
    (t : ℝ) (u v : Q) :
    q ((t : ℂ) • u) ((t : ℂ) • v) = (t : ℂ) ^ 2 * q u v := by
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Complex.conj_ofReal, RingHom.id_apply]
  ring

private theorem form_real_variation (q : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ)
    (hq : ∀ x y, star (q x y) = q y x) (u v : Q) (t : ℝ) :
    (q (u + (t : ℂ) • v) (u + (t : ℂ) • v)).re =
      (q u u).re + 2 * t * (q v u).re + t ^ 2 * (q v v).re := by
  have hcross : (q u v).re = (q v u).re := by
    have h := congrArg Complex.re (hq u v)
    simpa only [Complex.star_def, Complex.conj_re] using h
  simp only [map_add, map_smulₛₗ, RingHom.id_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hcross]
  ring

private theorem norm_real_variation (x y : H) (t : ℝ) :
    ‖x + (t : ℂ) • y‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * t * (⟪y, x⟫_ℂ).re + t ^ 2 * ‖y‖ ^ 2 := by
  have hcross : (⟪x, y⟫_ℂ).re = (⟪y, x⟫_ℂ).re := by
    have h := congrArg Complex.re (inner_conj_symm x y)
    simpa only [Complex.conj_re] using h.symm
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
  change ‖x‖ ^ 2 + 2 * ((t : ℂ) * ⟪x, y⟫_ℂ).re +
    (‖(t : ℂ)‖ * ‖y‖) ^ 2 = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs, hcross]
  ring

/-- Normalization converts a lower bound on the unit sphere to the
homogeneous Rayleigh inequality throughout the linear sector. -/
theorem rayleigh_lower_of_normalized_minimum
    (L : Q →ₗ[ℂ] H) (hL : Function.Injective L)
    (q : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ) (S : Submodule ℂ Q) (E : ℝ)
    (hmin : ∀ v ∈ S, ‖L v‖ = 1 → E ≤ (q v v).re) :
    ∀ v ∈ S, E * ‖L v‖ ^ 2 ≤ (q v v).re := by
  intro v hv
  by_cases hz : L v = 0
  · have hvzero : v = 0 := hL (hz.trans (map_zero L).symm)
    subst v
    simp
  have hn : 0 < ‖L v‖ := norm_pos_iff.mpr hz
  let w : Q := ((‖L v‖⁻¹ : ℝ) : ℂ) • v
  have hw : w ∈ S := S.smul_mem _ hv
  have hwnorm : ‖L w‖ = 1 := by
    change ‖L (((‖L v‖⁻¹ : ℝ) : ℂ) • v)‖ = 1
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hbound := hmin w hw hwnorm
  have he : (q w w).re = ‖L v‖⁻¹ ^ 2 * (q v v).re := by
    rw [show q w w = ((‖L v‖⁻¹ : ℝ) : ℂ) ^ 2 * q v v from
      form_real_smul q _ v v]
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  rw [he] at hbound
  have hm := mul_le_mul_of_nonneg_right hbound (sq_nonneg ‖L v‖)
  have hc : (‖L v‖⁻¹ ^ 2 * (q v v).re) * ‖L v‖ ^ 2 = (q v v).re := by
    field_simp [hn.ne']
  exact hm.trans_eq hc

/-- The weak eigenvalue equation follows from the homogeneous Rayleigh
inequality and equality at one normalized vector. -/
theorem weak_of_rayleigh_lower
    (L : Q →ₗ[ℂ] H) (q : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ)
    (hq : ∀ x y, star (q x y) = q y x) (S : Submodule ℂ Q)
    {u : Q} {E : ℝ} (hu : u ∈ S) (hnorm : ‖L u‖ = 1)
    (hE : (q u u).re = E)
    (hlower : ∀ v ∈ S, E * ‖L v‖ ^ 2 ≤ (q v v).re) :
    ∀ v ∈ S, q v u = (E : ℂ) * ⟪L v, L u⟫_ℂ := by
  have hre : ∀ v ∈ S, (q v u).re = E * (⟪L v, L u⟫_ℂ).re := by
    intro v hv
    have hpoly : ∀ t : ℝ, 0 ≤
        t * (2 * ((q v u).re - E * (⟪L v, L u⟫_ℂ).re)) +
        t ^ 2 * ((q v v).re - E * ‖L v‖ ^ 2) := by
      intro t
      have h := hlower (u + (t : ℂ) • v) (S.add_mem hu (S.smul_mem _ hv))
      rw [form_real_variation q hq, map_add, map_smul, norm_real_variation,
        hnorm, hE] at h
      nlinarith only [h]
    have h := linear_zero hpoly
    linarith only [h]
  intro v hv
  have hr := hre v hv
  have hi := hre (Complex.I • v) (S.smul_mem _ hv)
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
    inner_smul_left, Complex.conj_I, Complex.neg_re, Complex.I_re,
    Complex.neg_im, Complex.I_im, Complex.mul_re, zero_mul, neg_mul,
    one_mul, neg_sub, sub_zero, neg_neg] at hi
  apply Complex.ext
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hr
  · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using hi

/-- A normalized quadratic minimizer on a complex linear sector is a
weak eigenvector on that sector. In particular the sector may be the
fermionic reference subspace. -/
theorem weak_of_normalized_minimum
    (L : Q →ₗ[ℂ] H) (hL : Function.Injective L)
    (q : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ)
    (hq : ∀ x y, star (q x y) = q y x) (S : Submodule ℂ Q)
    {u : Q} {E : ℝ} (hu : u ∈ S) (hnorm : ‖L u‖ = 1)
    (hE : (q u u).re = E)
    (hmin : ∀ v ∈ S, ‖L v‖ = 1 → E ≤ (q v v).re) :
    ∀ v ∈ S, q v u = (E : ℂ) * ⟪L v, L u⟫_ℂ :=
  weak_of_rayleigh_lower L q hq S hu hnorm hE
    (rayleigh_lower_of_normalized_minimum L hL q S E hmin)

end PfHk.FermionicVariational
