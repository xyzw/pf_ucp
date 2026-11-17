import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Field

/-!
Ported with attribution from `claude_lean/QEDFT/Repair/Multipliers.lean`.
The normalization parameter is renamed `q` to match the current manuscript.
Historical numerical line references below refer to the earlier source snapshot.
Current anchors are `lem-one-electron-current-repair`,
`one-electron-repair-exact-energy`, and `lem-fermionic-current-repair`.
These theorems prove pointwise differential and integral algebra. Sobolev extension,
trace-class channel construction and form-domain passage remain separate inputs.
-/

/-!
# The six current-repair multipliers (lem-one-electron-current-repair)

Paper: `qedft.tex`, statement lines 1822-1843, proof lines 5178-5229; N-body analogue 5353-5362.
Survey items: B15 (normalization / connection / metric of the six multipliers).

For `q > 3‖v‖_∞` the paper uses the six multiplication operators
`K_{μ,σ}(x) = (1/√6) √(1 + 3 σ v_μ(x)/q) · exp(i σ q x_μ)`, `μ = 1,2,3`, `σ = ±1`, and claims

* `∑ |K_{μ,σ}|² = 1`                                           (normalization),
* `∑ conj(K_{μ,σ}) ∇K_{μ,σ} = i v`                             (connection),
* `∑ |∇K_{μ,σ}|² = L² + (3/(4L²)) ∑_μ |∇v_μ|²/(1 - 9 v_μ²/L²)` (metric; line 5360, and with the
  kinetic prefactor `1/2` the `3/(8L²)` of line 5205).

We verify these pointwise, with genuine partial derivatives (derivatives along coordinate lines
`s ↦ x + s e_ν`, expressed through `HasDerivAt`).
-/

namespace GptLean.Multipliers

open Complex
open scoped ComplexConjugate

/-! ### Amplitude-phase calculus in one real variable -/

/-- Value of an amplitude-phase function `c √w · e^{iθ}`. -/
noncomputable def apVal (c w θ : ℝ) : ℂ := ((c * √w : ℝ) : ℂ) * cexp (I * (θ : ℂ))

/-- Derivative of `t ↦ c √(w t) · e^{i φ t}` expressed through `w, w' , θ = φ, φ'`. -/
noncomputable def apDeriv (c w w' θ φ' : ℝ) : ℂ :=
  (((c * (w' / (2 * √w)) : ℝ) : ℂ) + I * ((c * √w * φ' : ℝ) : ℂ)) * cexp (I * (θ : ℂ))

/-- Survey B15 ("amplitude-phase lemma"), used in the proof of lem-one-electron-current-repair
(qedft.tex 5181-5196): if `w, φ` are real functions differentiable at `s` and `w s > 0`, then
`K(t) = c √(w t) e^{i φ(t)}` is differentiable at `s` with
`K'(s) = (c w'/(2√w) + i c √w φ') e^{iφ}`. -/
theorem hasDerivAt_apVal {w φ : ℝ → ℝ} {w' φ' s : ℝ} (c : ℝ)
    (hw : HasDerivAt w w' s) (hφ : HasDerivAt φ φ' s) (hpos : 0 < w s) :
    HasDerivAt (fun t : ℝ => apVal c (w t) (φ t)) (apDeriv c (w s) w' (φ s) φ') s := by
  have h1 : HasDerivAt (fun t => c * √(w t)) (c * (w' / (2 * √(w s)))) s :=
    (hw.sqrt hpos.ne').const_mul c
  have h2 : HasDerivAt (fun t : ℝ => cexp (I * (φ t : ℂ)))
      (cexp (I * (φ s : ℂ)) * (I * (φ' : ℂ))) s :=
    (hφ.ofReal_comp.const_mul I).cexp
  have h3 : HasDerivAt (fun t : ℝ => ((c * √(w t) : ℝ) : ℂ) * cexp (I * (φ t : ℂ))) _ s :=
    h1.ofReal_comp.mul h2
  unfold apVal apDeriv
  exact h3.congr_deriv (by push_cast; ring)

private lemma conj_mul_self_exp (θ : ℝ) : conj (cexp (I * (θ : ℂ))) * cexp (I * (θ : ℂ)) = 1 := by
  rw [← normSq_eq_conj_mul_self, ← Complex.sq_norm, norm_exp_I_mul_ofReal]
  simp

/-- `|c √w e^{iθ}|² = c² w` for `w ≥ 0` (pointwise weight of a multiplier; B15(a)). -/
theorem norm_sq_apVal {c w θ : ℝ} (hw : 0 ≤ w) : ‖apVal c w θ‖ ^ 2 = c ^ 2 * w := by
  unfold apVal
  rw [norm_mul, norm_exp_I_mul_ofReal, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    mul_pow, Real.sq_sqrt hw]

/-- Survey B15 (amplitude-phase lemma, connection part): for `K = c√w e^{iφ}`,
`conj(K) K' = c² w'/2 + i c² w φ'`. -/
theorem conj_apVal_mul_apDeriv {c w w' θ φ' : ℝ} (hw : 0 < w) :
    conj (apVal c w θ) * apDeriv c w w' θ φ'
      = ((c ^ 2 * (w' / 2) : ℝ) : ℂ) + I * ((c ^ 2 * w * φ' : ℝ) : ℂ) := by
  have hs : √w ≠ 0 := (Real.sqrt_pos.2 hw).ne'
  have hss : √w * √w = w := Real.mul_self_sqrt hw.le
  have e1 : c * √w * (c * (w' / (2 * √w))) = c ^ 2 * (w' / 2) := by
    field_simp
  have e2 : c * √w * (c * √w * φ') = c ^ 2 * w * φ' := by
    calc c * √w * (c * √w * φ') = c ^ 2 * (√w * √w) * φ' := by ring
      _ = c ^ 2 * w * φ' := by rw [hss]
  unfold apVal apDeriv
  rw [map_mul, conj_ofReal]
  calc ((c * √w : ℝ) : ℂ) * conj (cexp (I * (θ : ℂ)))
        * ((((c * (w' / (2 * √w)) : ℝ) : ℂ) + I * ((c * √w * φ' : ℝ) : ℂ)) * cexp (I * (θ : ℂ)))
      = (((c * √w * (c * (w' / (2 * √w))) : ℝ) : ℂ) + I * ((c * √w * (c * √w * φ') : ℝ) : ℂ))
        * (conj (cexp (I * (θ : ℂ))) * cexp (I * (θ : ℂ))) := by push_cast; ring
    _ = _ := by rw [conj_mul_self_exp, mul_one, e1, e2]

/-- Survey B15 (amplitude-phase lemma, metric part): for `K = c√w e^{iφ}`,
`|K'|² = c² w'²/(4w) + c² w φ'²`. -/
theorem norm_sq_apDeriv {c w w' θ φ' : ℝ} (hw : 0 < w) :
    ‖apDeriv c w w' θ φ'‖ ^ 2 = c ^ 2 * (w' ^ 2 / (4 * w)) + c ^ 2 * w * φ' ^ 2 := by
  have hs : √w ≠ 0 := (Real.sqrt_pos.2 hw).ne'
  have hss : √w ^ 2 = w := Real.sq_sqrt hw.le
  unfold apDeriv
  rw [norm_mul, norm_exp_I_mul_ofReal, mul_one, Complex.sq_norm, mul_comm I, normSq_add_mul_I]
  have e1 : (c * (w' / (2 * √w))) ^ 2 = c ^ 2 * (w' ^ 2 / (4 * w)) := by
    calc (c * (w' / (2 * √w))) ^ 2 = c ^ 2 * (w' ^ 2 / (4 * √w ^ 2)) := by
          field_simp; ring
      _ = _ := by rw [hss]
  have e2 : (c * √w * φ') ^ 2 = c ^ 2 * w * φ' ^ 2 := by
    calc (c * √w * φ') ^ 2 = c ^ 2 * (√w ^ 2) * φ' ^ 2 := by ring
      _ = _ := by rw [hss]
  rw [e1, e2]

/-! ### The six multipliers `K_{μ,σ}` -/

/-- The sign `σ = ±1` attached to a Boolean label (`true ↦ +1`, `false ↦ -1`). -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The weight factor `1 + 3 σ v_μ(y)/q` under the square root of `K_{μ,σ}`. -/
noncomputable def amp (q : ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ) (k : Fin 3 × Bool)
    (y : Fin 3 → ℝ) : ℝ :=
  1 + 3 * sgn k.2 * v y k.1 / q

/-- The six multipliers of qedft.tex 5183-5187, indexed by `k = (μ, σ) ∈ Fin 3 × Bool`. -/
noncomputable def K (q : ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ) (k : Fin 3 × Bool)
    (y : Fin 3 → ℝ) : ℂ :=
  apVal (1 / √6) (amp q v k y) (sgn k.2 * q * y k.1)

/-- Unfolding of the definition: `K_{μ,σ}(y) = (1/√6) √(1 + 3σ v_μ(y)/q) e^{iσL y_μ}`, exactly the
formula displayed at qedft.tex 5183-5187. -/
theorem K_apply (q : ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ) (μ : Fin 3) (b : Bool) (y : Fin 3 → ℝ) :
    K q v (μ, b) y = ((1 / √6 * √(1 + 3 * sgn b * v y μ / q) : ℝ) : ℂ)
      * cexp (I * ((sgn b * q * y μ : ℝ) : ℂ)) := rfl

/-- Partial derivative `∂_ν f (x)` of a complex function on `ℝ³`, as the derivative along the
coordinate line `s ↦ x + s e_ν`. -/
noncomputable def pderiv (f : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) (ν : Fin 3) : ℂ :=
  deriv (fun s : ℝ => f (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ))) 0

/-- Explicit value of `∂_ν K_{μ,σ}(x)` when `∂_ν v_μ(x) = dv μ ν`. -/
noncomputable def dK (q : ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ) (dv : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) (k : Fin 3 × Bool) (ν : Fin 3) : ℂ :=
  apDeriv (1 / √6) (amp q v k x) (3 * sgn k.2 * dv k.1 ν / q) (sgn k.2 * q * x k.1)
    (sgn k.2 * q * (if k.1 = ν then 1 else 0))

private lemma inv_sqrt_six_sq : (1 / √6 : ℝ) ^ 2 = 1 / 6 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

/-- The weights are positive when `3|v_μ(y)| < q` (this is the paper's requirement
`q > 3‖v‖_∞`, qedft.tex 5181). -/
theorem amp_pos {q : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ} {y : Fin 3 → ℝ} (hL : 0 < q)
    (k : Fin 3 × Bool) (h : 3 * |v y k.1| < q) : 0 < amp q v k y := by
  have h1 := abs_lt.1 (show |3 * v y k.1| < q by rwa [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)])
  have e : amp q v k y = (q + 3 * sgn k.2 * v y k.1) / q := by
    unfold amp; field_simp
  rw [e]
  apply div_pos _ hL
  rcases k with ⟨μ, b⟩
  cases b <;> simp only [sgn] <;> norm_num <;> linarith [h1.1, h1.2]

/-- **B15(a), normalization** (qedft.tex 5193, first identity): `∑_{μ,σ} |K_{μ,σ}(y)|² = 1`. -/
theorem sum_norm_sq_K {q : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ} {y : Fin 3 → ℝ} (hL : 0 < q)
    (h : ∀ μ, 3 * |v y μ| < q) : ∑ k, ‖K q v k y‖ ^ 2 = 1 := by
  have hk : ∀ k, ‖K q v k y‖ ^ 2 = 1 / 6 * amp q v k y := fun k => by
    unfold K; rw [norm_sq_apVal (amp_pos hL k (h k.1)).le, inv_sqrt_six_sq]
  simp only [hk, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, amp, sgn]
  simp only [ite_true, Bool.false_eq_true, ite_false]
  ring

/-- The multipliers are differentiable along coordinate lines, with the explicit derivative `dK`
(this makes `pderiv` below a genuine partial derivative). -/
theorem hasDerivAt_K {q : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ} {dv : Fin 3 → Fin 3 → ℝ}
    {x : Fin 3 → ℝ} (hL : 0 < q) (h : ∀ μ, 3 * |v x μ| < q)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ)
      (dv μ ν) 0) (k : Fin 3 × Bool) (ν : Fin 3) :
    HasDerivAt (fun s : ℝ => K q v k (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)))
      (dK q v dv x k ν) 0 := by
  have h0 : x + (0 : ℝ) • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ) = x := by simp
  have hw : HasDerivAt (fun s : ℝ => amp q v k (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)))
      (3 * sgn k.2 * dv k.1 ν / q) 0 := by
    unfold amp
    exact (((hv k.1 ν).const_mul (3 * sgn k.2)).div_const q).const_add 1
  have hφ : HasDerivAt
      (fun s : ℝ => sgn k.2 * q * (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) k.1)
      (sgn k.2 * q * (if k.1 = ν then 1 else 0)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => x k.1 + s * (if k.1 = ν then (1 : ℝ) else 0))
        (if k.1 = ν then (1 : ℝ) else 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (if k.1 = ν then (1 : ℝ) else 0)).const_add
        (x k.1)
    have h2 := h1.const_mul (sgn k.2 * q)
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp [Pi.single_apply]
  have hpos : 0 < amp q v k (x + (0 : ℝ) • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) := by
    rw [h0]; exact amp_pos hL k (h k.1)
  have := hasDerivAt_apVal (1 / √6) hw hφ hpos
  simp only [h0] at this
  exact this

/-- `pderiv (K_k) x ν` equals the explicit `dK`. -/
theorem pderiv_K {q : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ} {dv : Fin 3 → Fin 3 → ℝ}
    {x : Fin 3 → ℝ} (hL : 0 < q) (h : ∀ μ, 3 * |v x μ| < q)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ)
      (dv μ ν) 0) (k : Fin 3 × Bool) (ν : Fin 3) :
    pderiv (K q v k) x ν = dK q v dv x k ν :=
  (hasDerivAt_K hL h hv k ν).deriv

/-- **B15(b), connection** (qedft.tex 5194-5195, second identity; N-body form 5358):
`∑_{μ,σ} conj(K_{μ,σ}) ∂_ν K_{μ,σ} = i v_ν` at every point where `3|v_μ| < q` and `v` has partial
derivatives.  The real parts `σ ∂_ν v_μ/(4L)` cancel between `σ = ±1`. -/
theorem sum_conj_K_mul_pderiv {q : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ} {dv : Fin 3 → Fin 3 → ℝ}
    {x : Fin 3 → ℝ} (hL : 0 < q) (h : ∀ μ, 3 * |v x μ| < q)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ)
      (dv μ ν) 0) (ν : Fin 3) :
    ∑ k, conj (K q v k x) * pderiv (K q v k) x ν = I * (v x ν : ℂ) := by
  have hk : ∀ k : Fin 3 × Bool, conj (K q v k x) * pderiv (K q v k) x ν
      = ((1 / 6 * (3 * sgn k.2 * dv k.1 ν / q / 2) : ℝ) : ℂ)
        + I * ((1 / 6 * amp q v k x * (sgn k.2 * q * (if k.1 = ν then 1 else 0)) : ℝ) : ℂ) :=
    fun k => by
      rw [pderiv_K hL h hv, dK, K, conj_apVal_mul_apDeriv (amp_pos hL k (h k.1)), inv_sqrt_six_sq]
  have hpair : ∀ μ : Fin 3,
      conj (K q v (μ, true) x) * pderiv (K q v (μ, true)) x ν
        + conj (K q v (μ, false) x) * pderiv (K q v (μ, false)) x ν
      = if μ = ν then I * (v x μ : ℂ) else 0 := fun μ => by
    have hLc : (q : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    rw [hk, hk]
    simp only [amp, sgn, ite_true, Bool.false_eq_true, ite_false]
    split_ifs
    · push_cast; field_simp; ring
    · push_cast; ring
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, hpair]
  simp

/-- Pointwise form of B15(c): `∑_σ |∂_ν K_{μ,σ}|² = (L²/3) δ_{μν}
  + (3/(4L²)) (∂_ν v_μ)²/(1 - 9 v_μ²/L²)`, using `1/(1+a) + 1/(1-a) = 2/(1-a²)`. -/
theorem norm_sq_pderiv_pair {q : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ} {dv : Fin 3 → Fin 3 → ℝ}
    {x : Fin 3 → ℝ} (hL : 0 < q) (h : ∀ μ, 3 * |v x μ| < q)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ)
      (dv μ ν) 0) (μ ν : Fin 3) :
    ‖pderiv (K q v (μ, true)) x ν‖ ^ 2 + ‖pderiv (K q v (μ, false)) x ν‖ ^ 2
      = (if μ = ν then q ^ 2 / 3 else 0)
        + 3 / (4 * q ^ 2) * ((dv μ ν) ^ 2 / (1 - 9 * (v x μ) ^ 2 / q ^ 2)) := by
  have hp := amp_pos hL (μ, true) (h μ)
  have hm := amp_pos hL (μ, false) (h μ)
  rw [pderiv_K hL h hv, pderiv_K hL h hv, dK, dK, norm_sq_apDeriv hp, norm_sq_apDeriv hm,
    inv_sqrt_six_sq]
  simp only [amp, sgn, ite_true, Bool.false_eq_true, ite_false] at hp hm ⊢
  have hL' : q ≠ 0 := hL.ne'
  have eA : 1 + 3 * 1 * v x μ / q = (q + 3 * v x μ) / q := by field_simp
  have eB : 1 + 3 * -1 * v x μ / q = (q - 3 * v x μ) / q := by field_simp; ring
  have eC : 1 - 9 * (v x μ) ^ 2 / q ^ 2 = (q + 3 * v x μ) * (q - 3 * v x μ) / q ^ 2 := by
    field_simp; ring
  rw [eA] at hp
  rw [eB] at hm
  have h1 : q + 3 * v x μ ≠ 0 := fun h0 => by simp [h0] at hp
  have h2 : q - 3 * v x μ ≠ 0 := fun h0 => by simp [h0] at hm
  rw [eA, eB, eC]
  split_ifs
  · field_simp; ring
  · field_simp; ring

/-- **B15(c), metric** (qedft.tex 5359-5361; with the kinetic prefactor `1/2` this is the
`L²/2 + (3/(8L²)) ∑_μ |∇v_μ|²/(1-9v_μ²/L²)` of 5203-5207):
`∑_{μ,σ} |∇K_{μ,σ}|² = L² + (3/(4L²)) ∑_μ |∇v_μ|²/(1 - 9 v_μ²/L²)`. -/
theorem sum_norm_sq_pderiv_K {q : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ} {dv : Fin 3 → Fin 3 → ℝ}
    {x : Fin 3 → ℝ} (hL : 0 < q) (h : ∀ μ, 3 * |v x μ| < q)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ)
      (dv μ ν) 0) :
    ∑ k, ∑ ν, ‖pderiv (K q v k) x ν‖ ^ 2
      = q ^ 2 + 3 / (4 * q ^ 2)
          * ∑ μ, (∑ ν, (dv μ ν) ^ 2) / (1 - 9 * (v x μ) ^ 2 / q ^ 2) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ← Finset.sum_add_distrib, norm_sq_pderiv_pair hL h hv]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum, ← Finset.sum_div]
  rw [nsmul_eq_mul]
  push_cast
  ring

/-! ### B16: the choice of `L²` and the constant 36 -/

/-- B16(i) (qedft.tex 5181, 5213-5215): with `L² = max{36V², √G}` and `V > 0` one has
`q ≥ 6V`, hence the admissibility condition `q > 3‖v‖_∞`. -/
theorem three_mul_lt_sqrt_max {V : ℝ} (hV : 0 < V) (B : ℝ) :
    3 * V < √(max (36 * V ^ 2) B) := by
  have h6 : 6 * V ≤ √(max (36 * V ^ 2) B) := by
    rw [Real.le_sqrt' (by positivity)]
    calc (6 * V) ^ 2 = 36 * V ^ 2 := by ring
      _ ≤ _ := le_max_left _ _
  linarith

/-- B16(ii) (qedft.tex 5216-5217): if `|t| ≤ V` and `L² ≥ 36V²`, `V > 0`, the denominators
`1 - 9t²/L²` are at least `3/4`. -/
theorem denom_ge {V t q2 : ℝ} (hV : 0 < V) (ht : |t| ≤ V) (hL : 36 * V ^ 2 ≤ q2) :
    3 / 4 ≤ 1 - 9 * t ^ 2 / q2 := by
  have hL2 : 0 < q2 := lt_of_lt_of_le (by positivity) hL
  have ht2 : t ^ 2 ≤ V ^ 2 := by
    rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) ht 2
  have : 9 * t ^ 2 / q2 ≤ 1 / 4 := by
    rw [div_le_iff₀ hL2]; nlinarith
  linarith

/-- B16(iii), scalar chain of qedft.tex 5218-5224 with the paper's constants: if
`L² = max{36V², √G}` and the kinetic remainder `S` (standing for
`∑_μ ∫ρ|∇v_μ|²/(1-9v_μ²/L²)`) satisfies `S ≤ (4/3) G`, then
`L²/2 + (3/(8L²)) S ≤ L²/2 + G/(2L²) ≤ L² ≤ 36V² + √G`. -/
theorem repair_cost_chain {V G S q2 : ℝ} (hV : 0 < V) (hG : 0 ≤ G)
    (hL2 : q2 = max (36 * V ^ 2) (√G)) (hS : S ≤ 4 / 3 * G) :
    q2 / 2 + 3 / (8 * q2) * S ≤ q2 / 2 + G / (2 * q2)
      ∧ q2 / 2 + G / (2 * q2) ≤ q2 ∧ q2 ≤ 36 * V ^ 2 + √G := by
  have hpos : 0 < q2 := by
    rw [hL2]; exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hsq : √G ≤ q2 := by rw [hL2]; exact le_max_right _ _
  have hGL : G ≤ q2 ^ 2 := by
    calc G = √G ^ 2 := (Real.sq_sqrt hG).symm
      _ ≤ q2 ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg G) hsq 2
  refine ⟨?_, ?_, ?_⟩
  · have : 3 / (8 * q2) * S ≤ G / (2 * q2) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  · have : G / (2 * q2) ≤ q2 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  · rw [hL2]
    exact max_le (le_add_of_nonneg_right (Real.sqrt_nonneg G))
      (le_add_of_nonneg_left (by positivity))

/-- N-body variant (qedft.tex 5353-5362, survey B16): with `L² = max{36V², M}` and
`S ≤ (4/3) M²`: `L² + (3/(4L²)) S ≤ L² + M²/L² ≤ 36V² + 2M`. -/
theorem nbody_metric_chain {V M S q2 : ℝ} (hV : 0 < V) (hM : 0 ≤ M)
    (hL2 : q2 = max (36 * V ^ 2) M) (hS : S ≤ 4 / 3 * M ^ 2) :
    q2 + 3 / (4 * q2) * S ≤ q2 + M ^ 2 / q2 ∧ q2 + M ^ 2 / q2 ≤ 36 * V ^ 2 + 2 * M := by
  have hpos : 0 < q2 := by
    rw [hL2]; exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hML : M ≤ q2 := by rw [hL2]; exact le_max_right _ _
  have hle : q2 ≤ 36 * V ^ 2 + M := by
    rw [hL2]
    exact max_le (le_add_of_nonneg_right hM) (le_add_of_nonneg_left (by positivity))
  constructor
  · have : 3 / (4 * q2) * S ≤ M ^ 2 / q2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hpos]
      nlinarith
    linarith
  · have : M ^ 2 / q2 ≤ M := by
      rw [div_le_iff₀ hpos]; nlinarith
    linarith

/-- Elementary step behind "the denominators are at least 3/4" (qedft.tex 5216-5217):
for `a ≥ 0` and `d ≥ 3/4`, `a/d ≤ (4/3) a`.  Note `(3/8)(4/3) = 1/2` and `(3/4)(4/3) = 1`. -/
theorem div_le_four_thirds {a d : ℝ} (ha : 0 ≤ a) (hd : 3 / 4 ≤ d) : a / d ≤ 4 / 3 * a := by
  have hd0 : 0 < d := by linarith
  rw [div_le_iff₀ hd0]; nlinarith

/-- **The display qedft.tex 5358-5362 (proof of lem-fermionic-current-repair), survey B15+B16**:
put `V ≥ |v_μ(x)|`, `V > 0`, `M² ≥ ∑_{μ,ν} (∂_ν v_μ(x))²` (Frobenius norm of `∇v`) and
`L² = max{36V², M}`.  Then the unit vector `k = (K_{μ,σ})` of the six multipliers satisfies
`|∇k(x)|² = ∑_{μ,σ,ν} |∂_ν K_{μ,σ}(x)|² ≤ 36V² + 2M`. -/
theorem sum_norm_sq_pderiv_K_le {V M : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {dv : Fin 3 → Fin 3 → ℝ} {x : Fin 3 → ℝ} (hV : 0 < V) (hM : 0 ≤ M)
    (hvV : ∀ μ, |v x μ| ≤ V) (hdv : ∑ μ, ∑ ν, (dv μ ν) ^ 2 ≤ M ^ 2)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ)
      (dv μ ν) 0) :
    ∑ k, ∑ ν, ‖pderiv (K (√(max (36 * V ^ 2) M)) v k) x ν‖ ^ 2 ≤ 36 * V ^ 2 + 2 * M := by
  have h3 := three_mul_lt_sqrt_max hV M
  have hL : 0 < √(max (36 * V ^ 2) M) := by linarith
  have hLsq : √(max (36 * V ^ 2) M) ^ 2 = max (36 * V ^ 2) M :=
    Real.sq_sqrt (le_trans (by positivity) (le_max_left _ _))
  have h : ∀ μ, 3 * |v x μ| < √(max (36 * V ^ 2) M) := fun μ => by linarith [hvV μ]
  rw [sum_norm_sq_pderiv_K hL h hv, hLsq]
  have hS : ∑ μ, (∑ ν, (dv μ ν) ^ 2) / (1 - 9 * (v x μ) ^ 2 / max (36 * V ^ 2) M)
      ≤ 4 / 3 * M ^ 2 := by
    calc ∑ μ, (∑ ν, (dv μ ν) ^ 2) / (1 - 9 * (v x μ) ^ 2 / max (36 * V ^ 2) M)
        ≤ ∑ μ, 4 / 3 * ∑ ν, (dv μ ν) ^ 2 := Finset.sum_le_sum fun μ _ =>
          div_le_four_thirds (Finset.sum_nonneg fun ν _ => sq_nonneg _)
            (denom_ge hV (hvV μ) (le_max_left _ _))
      _ = 4 / 3 * ∑ μ, ∑ ν, (dv μ ν) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 / 3 * M ^ 2 := by linarith
  have hc := nbody_metric_chain hV hM rfl hS
  exact hc.1.trans hc.2

end GptLean.Multipliers
