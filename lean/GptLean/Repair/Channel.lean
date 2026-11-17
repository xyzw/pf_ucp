import GptLean.Repair.Multipliers
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Ported with attribution from `claude_lean/QEDFT/Repair/Channel.lean`.
The normalization parameter is renamed `q` to match the current manuscript.
Historical numerical line references below refer to the earlier source snapshot.
Current anchors are `lem-one-electron-current-repair`,
`one-electron-repair-exact-energy`, and `lem-fermionic-current-repair`.
These theorems prove pointwise differential and integral algebra. Sobolev extension,
trace-class channel construction and form-domain passage remain separate inputs.
-/

/-!
# The multiplier channel: energy, current and marginal identities behind the current repair

Paper: `qedft.tex`, Lemma 4.14 `lem-one-electron-current-repair` (statement 1822-1843, proof
5178-5229, exact energy identity `one-electron-repair-exact-energy` 5202-5209), Lemma 4.16
`lem-fermionic-current-repair` (statement 1874-1889, proof 5350-5379, cost
`fermionic-repair-cost` 1881-1885), and the covariant IMS identity 4956-4988.
Survey item B12.

All these proofs "expand `D(KΨ) = K DΨ - i (∇K) Ψ`" (l. 4958, 5200) for a finite family of
multiplication operators `K_α` and sum over `α`.  The algebra of that expansion is isolated here
in an abstract complex inner product space `H` (think: the fibre of the wave function over a
point `x` of configuration space, including the photon factor), where

* `ψ = Ψ(x)` and `u = (DΨ)(x)` is the value of one component of the covariant derivative,
* `K α, K' α : H →ₗ[ℂ] H` are the values of `K_α` and `∂K_α` (for the paper's multiplication
  operators these are scalars, see `channel_energy_scalar`),
* `v : H →ₗ[ℂ] H` is the value of one component of the velocity field,

and the only inputs are the paper's two identities (l. 5193-5195, 5367-5368)

* normalization `∑_α K_α* K_α = 1`,   hypothesis `hnorm : ∑ α, ⟪K α x, K α y⟫ = ⟪x, y⟫`;
* connection    `∑_α K_α* ∂K_α = i v`, hypothesis `hconn : ∑ α, ⟪K α x, K' α y⟫ = i ⟪x, v y⟫`.

The channel derivative is `u_α := K α u - i K' α ψ`, i.e. the value of `D(K_αΨ)`.  Integrating
the pointwise identities over `x` (and over the spectral decomposition of `Γ`) turns `½‖u‖²`
into the kinetic energy density, `Re⟪u, vψ⟫` into `j^c·v / N` (eq. `jc-def`, l. 1239-1241,
`j^c = N Re⟪Ψ, DΨ⟫_x`) and `‖ψ‖²` into `ρ / N` (l. 1233); this is how the paper's displayed
formulas arise from the identities below.

The inner product is linear in its second argument, as in the paper (l. 1869-1870).
-/

namespace GptLean.Repair

open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {α : Type*} [Fintype α]

/-! ### The three abstract identities (E), (J), (W) of survey item B12 -/

/-- **Normalization ⇒ density / norm preservation** (qedft.tex 5193 "The first identity proves
normalization, density preservation"; B12 (W) with `W = 1`): if `∑_α K_α* K_α = 1` then
`∑_α ‖K_α ψ‖² = ‖ψ‖²`. -/
theorem sum_norm_sq_apply (K : α → H →ₗ[ℂ] H)
    (hnorm : ∀ x y, ∑ a, inner ℂ (K a x) (K a y) = inner ℂ x y) (u : H) :
    ∑ a, ‖K a u‖ ^ 2 = ‖u‖ ^ 2 := by
  have h : ∀ w : H, ‖w‖ ^ 2 = (inner ℂ w w).re := fun w =>
    (inner_self_eq_norm_sq (𝕜 := ℂ) w).symm
  simp_rw [h]
  rw [← Complex.re_sum, hnorm]

/-- **B12 (E), the channel energy identity** (the pointwise algebra of qedft.tex 5199-5209 and
5373-5376): with `∑ K_α* K_α = 1` and `∑ K_α* K'_α = i v`, the channel derivatives
`u_α = K_α u - i K'_α ψ` satisfy
`∑_α ‖u_α‖² = ‖u‖² + 2 Re⟪u, vψ⟫ + ∑_α ‖K'_α ψ‖²`.
No symmetry or commutativity is needed.  With `u = DΨ(x)`, `ψ = Ψ(x)`, integrating over `x` and
multiplying by `½` gives `ΔE = ∫ j^c·v + ½ ∑_α ‖(∇K_α)Ψ‖²`. -/
theorem channel_energy (K K' : α → H →ₗ[ℂ] H) (v : H →ₗ[ℂ] H)
    (hnorm : ∀ x y, ∑ a, inner ℂ (K a x) (K a y) = inner ℂ x y)
    (hconn : ∀ x y, ∑ a, inner ℂ (K a x) (K' a y) = Complex.I * inner ℂ x (v y)) (u ψ : H) :
    ∑ a, ‖K a u - Complex.I • K' a ψ‖ ^ 2
      = ‖u‖ ^ 2 + 2 * (inner ℂ u (v ψ)).re + ∑ a, ‖K' a ψ‖ ^ 2 := by
  have hI : ∀ w : H, ‖Complex.I • w‖ = ‖w‖ := fun w => by simp [norm_smul]
  have hcross : ∑ a, (inner ℂ (K a u) (Complex.I • K' a ψ)).re = -(inner ℂ u (v ψ)).re := by
    simp_rw [inner_smul_right]
    rw [← Complex.re_sum, ← Finset.mul_sum, hconn, ← mul_assoc, Complex.I_mul_I, neg_one_mul,
      Complex.neg_re]
  simp_rw [norm_sub_sq (𝕜 := ℂ), hI, RCLike.re_to_complex]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hcross,
    sum_norm_sq_apply K hnorm u]
  ring

/-- **B12 (J), complex form**: for any `g` commuting with all `K_α` and `K'_α`,
`∑_α ⟪K_α ψ, g u_α⟫ = ⟪ψ, g u⟫ + ⟪ψ, v g ψ⟫`.  (Only the commutation relations are used.) -/
theorem channel_current_inner (K K' : α → H →ₗ[ℂ] H) (v : H →ₗ[ℂ] H)
    (hnorm : ∀ x y, ∑ a, inner ℂ (K a x) (K a y) = inner ℂ x y)
    (hconn : ∀ x y, ∑ a, inner ℂ (K a x) (K' a y) = Complex.I * inner ℂ x (v y))
    (g : H →ₗ[ℂ] H) (hgK : ∀ a x, g (K a x) = K a (g x)) (hgK' : ∀ a x, g (K' a x) = K' a (g x))
    (u ψ : H) :
    ∑ a, inner ℂ (K a ψ) (g (K a u - Complex.I • K' a ψ))
      = inner ℂ ψ (g u) + inner ℂ ψ (v (g ψ)) := by
  simp_rw [map_sub, map_smul, hgK, hgK', inner_sub_right, inner_smul_right]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, hconn, ← mul_assoc, Complex.I_mul_I,
    neg_one_mul, sub_neg_eq_add]

/-- **B12 (J), the current shift** (qedft.tex 5198-5199 "The second proves the current identity",
eq. `one-electron-repaired-constraints` l. 1829 `j^c_{Γ_v} = j^c_Γ + ρ_Γ v`; N-body l. 5375):
for a test operator `g` commuting with all `K_α`, `K'_α` and with `v`,
`∑_α Re⟪K_α ψ, g u_α⟫ = Re⟪ψ, g u⟫ + Re⟪ψ, g v ψ⟫`.
With `g` = multiplication by a test function, integrating over `x` gives
`∫ g·j^c_{Γ_v} = ∫ g·j^c_Γ + ∫ g ρ_Γ v`. -/
theorem channel_current (K K' : α → H →ₗ[ℂ] H) (v : H →ₗ[ℂ] H)
    (hnorm : ∀ x y, ∑ a, inner ℂ (K a x) (K a y) = inner ℂ x y)
    (hconn : ∀ x y, ∑ a, inner ℂ (K a x) (K' a y) = Complex.I * inner ℂ x (v y))
    (g : H →ₗ[ℂ] H) (hgK : ∀ a x, g (K a x) = K a (g x)) (hgK' : ∀ a x, g (K' a x) = K' a (g x))
    (hgv : ∀ x, g (v x) = v (g x)) (u ψ : H) :
    ∑ a, (inner ℂ (K a ψ) (g (K a u - Complex.I • K' a ψ))).re
      = (inner ℂ ψ (g u)).re + (inner ℂ ψ (g (v ψ))).re := by
  rw [← Complex.re_sum, channel_current_inner K K' v hnorm hconn g hgK hgK' u ψ, Complex.add_re,
    hgv]

/-- The shift term `⟪ψ, g v ψ⟫` in `channel_current` is real when `g` and `v` are symmetric and
commute (survey B12: "`⟨ψ, gvψ⟩` is real"; it is `∫ g ρ v`). -/
theorem inner_comp_symm_im (g v : H →ₗ[ℂ] H)
    (hg : ∀ x y, inner ℂ (g x) y = inner ℂ x (g y))
    (hv : ∀ x y, inner ℂ (v x) y = inner ℂ x (v y)) (hgv : ∀ x, g (v x) = v (g x)) (ψ : H) :
    (inner ℂ ψ (g (v ψ))).im = 0 := by
  rw [← Complex.conj_eq_iff_im, inner_conj_symm, hg, hv, hgv]

/-- **B12 (W), preservation of every observable commuting with the multipliers** (qedft.tex
5197-5198: density and photon reduced state; 5374-5377: configuration density, photon marginal,
Coulomb and radiation energies): if `W` commutes with all `K_α` and `∑ K_α* K_α = 1`, then
`∑_α ⟪K_α ψ, W K_α ψ⟫ = ⟪ψ, W ψ⟫`. -/
theorem channel_preserves (K : α → H →ₗ[ℂ] H)
    (hnorm : ∀ x y, ∑ a, inner ℂ (K a x) (K a y) = inner ℂ x y)
    (W : H →ₗ[ℂ] H) (hW : ∀ a x, W (K a x) = K a (W x)) (ψ : H) :
    ∑ a, inner ℂ (K a ψ) (W (K a ψ)) = inner ℂ ψ (W ψ) := by
  simp_rw [hW]
  exact hnorm ψ (W ψ)

/-! ### The covariant IMS identity as the special case `v = 0` -/

/-- **Covariant IMS identity** (qedft.tex 4956-4974, and `current-preserving-electronic-IMS`
5342-5348; B12 special case): for symmetric (real) multipliers `f_α` with `∑ f_α² = 1` and
`∑ f_α f'_α = 0` (the cross terms cancel, l. 4962-4968),
`∑_α ‖f_α u - i f'_α ψ‖² = ‖u‖² + ∑_α ‖f'_α ψ‖²`.
With `α = Bool`, `f = (η_L, η̃_L)` this is the identity displayed at l. 4971-4974 (cf.
`GptLean.PhotonLoss.covariant_ims`). -/
theorem covariant_ims_channel (f f' : α → H →ₗ[ℂ] H)
    (hf : ∀ a x y, inner ℂ (f a x) y = inner ℂ x (f a y))
    (hsq : ∀ x, ∑ a, f a (f a x) = x) (hcross : ∀ x, ∑ a, f a (f' a x) = 0) (u ψ : H) :
    ∑ a, ‖f a u - Complex.I • f' a ψ‖ ^ 2 = ‖u‖ ^ 2 + ∑ a, ‖f' a ψ‖ ^ 2 := by
  have hnorm : ∀ x y, ∑ a, inner ℂ (f a x) (f a y) = inner ℂ x y := fun x y => by
    simp_rw [hf, ← inner_sum, hsq]
  have hconn : ∀ x y, ∑ a, inner ℂ (f a x) (f' a y)
      = Complex.I * inner ℂ x ((0 : H →ₗ[ℂ] H) y) := fun x y => by
    simp_rw [hf, ← inner_sum, hcross]
    simp
  have h := channel_energy f f' 0 hnorm hconn u ψ
  simpa using h

/-- **Current preservation under the covariant IMS localization** (qedft.tex 5342-5348,
`current-preserving-electronic-IMS`): with `∑ f_α f'_α = 0` the current is unchanged,
`∑_α Re⟪f_α ψ, g (f_α u - i f'_α ψ)⟫ = Re⟪ψ, g u⟫` for every `g` commuting with the `f_α`,
`f'_α`. -/
theorem covariant_ims_current (f f' : α → H →ₗ[ℂ] H)
    (hf : ∀ a x y, inner ℂ (f a x) y = inner ℂ x (f a y))
    (hsq : ∀ x, ∑ a, f a (f a x) = x) (hcross : ∀ x, ∑ a, f a (f' a x) = 0)
    (g : H →ₗ[ℂ] H) (hgf : ∀ a x, g (f a x) = f a (g x)) (hgf' : ∀ a x, g (f' a x) = f' a (g x))
    (u ψ : H) :
    ∑ a, (inner ℂ (f a ψ) (g (f a u - Complex.I • f' a ψ))).re = (inner ℂ ψ (g u)).re := by
  have hnorm : ∀ x y, ∑ a, inner ℂ (f a x) (f a y) = inner ℂ x y := fun x y => by
    simp_rw [hf, ← inner_sum, hsq]
  have hconn : ∀ x y, ∑ a, inner ℂ (f a x) (f' a y)
      = Complex.I * inner ℂ x ((0 : H →ₗ[ℂ] H) y) := fun x y => by
    simp_rw [hf, ← inner_sum, hcross]
    simp
  have h := channel_current f f' 0 hnorm hconn g hgf hgf' (fun x => by simp) u ψ
  simpa using h

/-! ### Scalar multipliers and Lemma 4.14 (`one-electron-repair-exact-energy`) -/

/-- **B12 (E) for scalar multipliers**: complex numbers `k_α` (values of multiplication
operators at a point) with `∑ |k_α|² = 1` and `∑ conj(k_α) k'_α = i s`, `s` real, give
`∑_α ‖k_α u - i k'_α ψ‖² = ‖u‖² + 2 s Re⟪u, ψ⟫ + (∑_α |k'_α|²) ‖ψ‖²`.
This also shows that the hypotheses of `channel_energy` are satisfiable (non-vacuity). -/
theorem channel_energy_scalar (k k' : α → ℂ) (s : ℝ) (hnorm : ∑ a, ‖k a‖ ^ 2 = 1)
    (hconn : ∑ a, conj (k a) * k' a = Complex.I * s) (u ψ : H) :
    ∑ a, ‖k a • u - Complex.I • k' a • ψ‖ ^ 2
      = ‖u‖ ^ 2 + 2 * s * (inner ℂ u ψ).re + (∑ a, ‖k' a‖ ^ 2) * ‖ψ‖ ^ 2 := by
  have hk1 : ∑ a, conj (k a) * k a = 1 := by
    simp_rw [Complex.conj_mul']
    exact_mod_cast hnorm
  have hn : ∀ x y : H, ∑ a, inner ℂ ((k a • LinearMap.id : H →ₗ[ℂ] H) x)
      ((k a • LinearMap.id : H →ₗ[ℂ] H) y) = inner ℂ x y := fun x y => by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left, inner_smul_right,
      ← mul_assoc]
    rw [← Finset.sum_mul, Finset.sum_congr rfl fun a _ => mul_comm (k a) (conj (k a)), hk1,
      one_mul]
  have hc : ∀ x y : H, ∑ a, inner ℂ ((k a • LinearMap.id : H →ₗ[ℂ] H) x)
      ((k' a • LinearMap.id : H →ₗ[ℂ] H) y)
      = Complex.I * inner ℂ x (((s : ℂ) • LinearMap.id : H →ₗ[ℂ] H) y) := fun x y => by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left, inner_smul_right,
      ← mul_assoc]
    rw [← Finset.sum_mul, Finset.sum_congr rfl fun a _ => mul_comm (k' a) (conj (k a)), hconn]
  have h := channel_energy (fun a => k a • LinearMap.id) (fun a => k' a • LinearMap.id)
    ((s : ℂ) • LinearMap.id) hn hc u ψ
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at h
  rw [h, inner_smul_right, Complex.re_ofReal_mul]
  simp_rw [norm_smul, mul_pow]
  rw [Finset.sum_mul]
  ring

/-- One derivative direction `ν` of Lemma 4.14 (qedft.tex 5199-5201): at a point `x` with
`3|v_μ(x)| < q`, the six multipliers `K_k = K_{μ,σ}` of `GptLean.Multipliers` (l. 5183-5187) and
their partial derivatives `∂_ν K_k` satisfy, for the fibre vectors `u = (D_νΨ)(x)`, `ψ = Ψ(x)`,
`∑_k ‖K_k u - i (∂_ν K_k) ψ‖² = ‖u‖² + 2 v_ν(x) Re⟪u, ψ⟫ + (∑_k |∂_ν K_k(x)|²) ‖ψ‖²`.
Inputs: `sum_norm_sq_K` (normalization) and `sum_conj_K_mul_pderiv` (connection `= i v_ν`). -/
theorem one_electron_channel_energy {q : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {dv : Fin 3 → Fin 3 → ℝ} {x : Fin 3 → ℝ} (hL : 0 < q) (h : ∀ μ, 3 * |v x μ| < q)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ)
      (dv μ ν) 0) (u ψ : H) (ν : Fin 3) :
    ∑ k, ‖Multipliers.K q v k x • u
        - Complex.I • Multipliers.pderiv (Multipliers.K q v k) x ν • ψ‖ ^ 2
      = ‖u‖ ^ 2 + 2 * (v x ν * (inner ℂ u ψ).re)
        + (∑ k, ‖Multipliers.pderiv (Multipliers.K q v k) x ν‖ ^ 2) * ‖ψ‖ ^ 2 := by
  have := channel_energy_scalar (fun k => Multipliers.K q v k x)
    (fun k => Multipliers.pderiv (Multipliers.K q v k) x ν) (v x ν)
    (Multipliers.sum_norm_sq_K hL h) (Multipliers.sum_conj_K_mul_pderiv hL h hv ν) u ψ
  rw [this]
  ring

/-- **Lemma 4.14, eq. `one-electron-repair-exact-energy`** (qedft.tex 5199-5209), pointwise
form.  Let `u ν = (D_νΨ)(x)` be the three components of the covariant derivative at `x` and
`ψ = Ψ(x)`.  Then the kinetic energy density of the channel `Γ_{v,q} = ∑_k K_k Γ K_k*`,
`½ ∑_ν ∑_k ‖D_ν(K_kΨ)(x)‖²` with `D_ν(K_kΨ) = K_k D_νΨ - i (∂_ν K_k) Ψ` (l. 5200), equals
`½ ∑_ν ‖u ν‖² + ∑_ν v_ν(x) Re⟪u ν, ψ⟫ + [L²/2 + (3/(8L²)) ∑_μ |∇v_μ(x)|²/(1 - 9v_μ(x)²/L²)] ‖ψ‖²`.
Integrating over `x`, the first term is the original kinetic energy, the second is `∫ j^c_Γ·v`
(`j^c = Re⟪Ψ, DΨ⟫`, l. 1239-1241), and the last is `L²/2 + (3/(8L²)) ∑_μ ∫ ρ_Γ |∇v_μ|²/(1-9v_μ²/L²)`
(`ρ = ‖Ψ‖²`, l. 1233): exactly the display at l. 5202-5208.  Uses `sum_norm_sq_pderiv_K`
(metric) for the last coefficient; here `dv μ ν = ∂_ν v_μ(x)`. -/
theorem one_electron_repair_energy {q : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {dv : Fin 3 → Fin 3 → ℝ} {x : Fin 3 → ℝ} (hL : 0 < q) (h : ∀ μ, 3 * |v x μ| < q)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ)
      (dv μ ν) 0) (u : Fin 3 → H) (ψ : H) :
    1 / 2 * ∑ ν, ∑ k, ‖Multipliers.K q v k x • u ν
        - Complex.I • Multipliers.pderiv (Multipliers.K q v k) x ν • ψ‖ ^ 2
      = 1 / 2 * ∑ ν, ‖u ν‖ ^ 2 + ∑ ν, v x ν * (inner ℂ (u ν) ψ).re
        + (q ^ 2 / 2 + 3 / (8 * q ^ 2)
            * ∑ μ, (∑ ν, (dv μ ν) ^ 2) / (1 - 9 * (v x μ) ^ 2 / q ^ 2)) * ‖ψ‖ ^ 2 := by
  have hm : ∑ ν, ∑ k, ‖Multipliers.pderiv (Multipliers.K q v k) x ν‖ ^ 2
      = q ^ 2 + 3 / (4 * q ^ 2) * ∑ μ, (∑ ν, (dv μ ν) ^ 2) / (1 - 9 * (v x μ) ^ 2 / q ^ 2) := by
    rw [Finset.sum_comm]
    exact Multipliers.sum_norm_sq_pderiv_K hL h hv
  simp_rw [one_electron_channel_energy hL h hv (u _) ψ _]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hm]
  ring

/-- **Lemma 4.14 / Lemma 4.16 for `N = 1`, pointwise cost bound** (qedft.tex 5353-5362 with
`L² = max{36V², M}`, `V ≥ |v_μ(x)|`, `M² ≥ ∑_{μ,ν} (∂_ν v_μ(x))²`): the channel kinetic energy
density is at most the original one plus `∑_ν v_ν Re⟪u_ν, ψ⟫` (`= j^c·v`) plus
`½ (36V² + 2M) ‖ψ‖²`; the last term integrates (with `∫ ρ = 1`) to `18V² + M`, i.e. the
constant `C_1(V² + M)` of eq. `fermionic-repair-cost` for one electron with `C_1 = 18`.
Uses `sum_norm_sq_pderiv_K_le`. -/
theorem one_electron_repair_energy_le {V M : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {dv : Fin 3 → Fin 3 → ℝ} {x : Fin 3 → ℝ} (hV : 0 < V) (hM : 0 ≤ M)
    (hvV : ∀ μ, |v x μ| ≤ V) (hdv : ∑ μ, ∑ ν, (dv μ ν) ^ 2 ≤ M ^ 2)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ)
      (dv μ ν) 0) (u : Fin 3 → H) (ψ : H) :
    1 / 2 * ∑ ν, ∑ k, ‖Multipliers.K (√(max (36 * V ^ 2) M)) v k x • u ν
        - Complex.I • Multipliers.pderiv (Multipliers.K (√(max (36 * V ^ 2) M)) v k) x ν • ψ‖ ^ 2
      ≤ 1 / 2 * ∑ ν, ‖u ν‖ ^ 2 + ∑ ν, v x ν * (inner ℂ (u ν) ψ).re
        + 1 / 2 * (36 * V ^ 2 + 2 * M) * ‖ψ‖ ^ 2 := by
  have h3 := Multipliers.three_mul_lt_sqrt_max hV M
  have hL : 0 < √(max (36 * V ^ 2) M) := by linarith
  have h : ∀ μ, 3 * |v x μ| < √(max (36 * V ^ 2) M) := fun μ => by linarith [hvV μ]
  have hm : ∑ ν, ∑ k, ‖Multipliers.pderiv (Multipliers.K (√(max (36 * V ^ 2) M)) v k) x ν‖ ^ 2
      ≤ 36 * V ^ 2 + 2 * M := by
    rw [Finset.sum_comm]
    exact Multipliers.sum_norm_sq_pderiv_K_le hV hM hvV hdv hv
  simp_rw [one_electron_channel_energy hL h hv (u _) ψ _]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖ψ‖)
  linarith

/-! ### Lemma 4.16 (`fermionic-repair-cost`): several derivative directions, one lift -/

/-- **Lemma 4.16, exact energy identity** (qedft.tex 5364-5376): a single family of symmetric
multipliers `K_α` (the lift of `lem-symmetric-tensor-lift`) with `∑ K_α* K_α = 1` (l. 5367) and,
for every derivative direction `i` (in the paper `i = (electron, coordinate)`),
`∑_α K_α* ∇_i K_α = i v_i` (l. 5368, with `v_i` the velocity component at the `i`-th electron).
With `u i = (D_iΨ)(X)` and `ψ = Ψ(X)`,
`∑_i ∑_α ‖K_α u_i - i (∇_i K_α) ψ‖² = ∑_i ‖u_i‖² + 2 ∑_i Re⟪u_i, v_i ψ⟫ + ∑_{i,α} ‖(∇_i K_α) ψ‖²`;
integrated over `X` (and times `½`) this is `∫ j^c_Γ·v + ½ ∑_{i,α} ‖(∇_i K_α)Ψ‖²`, the
"kinetic remainder after expanding each covariant derivative" (l. 5376). -/
theorem fermionic_repair_energy_eq {ι : Type*} [Fintype ι] (K : α → H →ₗ[ℂ] H)
    (K' : ι → α → H →ₗ[ℂ] H) (v : ι → H →ₗ[ℂ] H)
    (hnorm : ∀ x y, ∑ a, inner ℂ (K a x) (K a y) = inner ℂ x y)
    (hconn : ∀ i x y, ∑ a, inner ℂ (K a x) (K' i a y) = Complex.I * inner ℂ x (v i y))
    (u : ι → H) (ψ : H) :
    ∑ i, ∑ a, ‖K a (u i) - Complex.I • K' i a ψ‖ ^ 2
      = ∑ i, ‖u i‖ ^ 2 + 2 * ∑ i, (inner ℂ (u i) (v i ψ)).re + ∑ i, ∑ a, ‖K' i a ψ‖ ^ 2 := by
  have hE : ∀ i, ∑ a, ‖K a (u i) - Complex.I • K' i a ψ‖ ^ 2
      = ‖u i‖ ^ 2 + 2 * (inner ℂ (u i) (v i ψ)).re + ∑ a, ‖K' i a ψ‖ ^ 2 :=
    fun i => channel_energy K (K' i) (v i) hnorm (hconn i) (u i) ψ
  simp_rw [hE]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **Lemma 4.16, eq. `fermionic-repair-cost`, pointwise form** (qedft.tex 1881-1885 and
5364-5377): under the hypotheses of `fermionic_repair_energy_eq` and the metric bound
`∑_{i,α} ‖(∇_i K_α) ψ‖² ≤ Cl ‖ψ‖²` (l. 5369, `∑_{i,α} |∇_i K_α|² ≤ C_N(V² + M) =: Cl` for the
lift; for multiplication operators the left side is `∑_{i,α} |∇_i K_α(X)|² ‖ψ‖²`),
`½ ∑_{i,α} ‖K_α u_i - i (∇_i K_α) ψ‖² ≤ ½ ∑_i ‖u_i‖² + ∑_i Re⟪u_i, v_i ψ⟫ + ½ Cl ‖ψ‖²`.
Integrated over `X`: `Tr(H^{0,0}Γ_v) ≤ Tr(H^{0,0}Γ) + ∫ j^c_Γ·v + ½ Cl`, since `‖ψ‖²`
integrates to `Tr Γ = 1`; with `Cl = C_N(V² + M)` this is eq. `fermionic-repair-cost` (the
factor `½` is absorbed into `C_N`).  The Coulomb and radiation energies are unchanged by
`channel_preserves`. -/
theorem fermionic_repair_energy {ι : Type*} [Fintype ι] (K : α → H →ₗ[ℂ] H)
    (K' : ι → α → H →ₗ[ℂ] H) (v : ι → H →ₗ[ℂ] H)
    (hnorm : ∀ x y, ∑ a, inner ℂ (K a x) (K a y) = inner ℂ x y)
    (hconn : ∀ i x y, ∑ a, inner ℂ (K a x) (K' i a y) = Complex.I * inner ℂ x (v i y))
    (u : ι → H) (ψ : H) (Cl : ℝ) (hmetric : ∑ i, ∑ a, ‖K' i a ψ‖ ^ 2 ≤ Cl * ‖ψ‖ ^ 2) :
    1 / 2 * ∑ i, ∑ a, ‖K a (u i) - Complex.I • K' i a ψ‖ ^ 2
      ≤ 1 / 2 * ∑ i, ‖u i‖ ^ 2 + ∑ i, (inner ℂ (u i) (v i ψ)).re + 1 / 2 * Cl * ‖ψ‖ ^ 2 := by
  rw [fermionic_repair_energy_eq K K' v hnorm hconn u ψ]
  linarith

end GptLean.Repair
