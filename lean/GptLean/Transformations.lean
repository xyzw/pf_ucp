import GptLean.DFT
import GptLean.Repair.Channel
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
Appendix `app-transformation-properties`.
Functional covariance proofs are adapted with attribution from
`claude_lean/QEDFT/DFT/Covariance.lean` to this project's StateModel API.
Historical line references in those ported comments refer to that source.
The algebra is valid also for empty fibers and infinite functional values.

Concrete PF unitary actions, weak product rules, preservation of their form
domains and bounded actions on density/potential spaces remain analytic inputs.
The Hilbert-space norm expansions below prove the gauge and displacement
energy/current algebra from those inputs, not the operator-domain statements.
-/

namespace GptLean.Transformations

open GptLean.DFT

section LevyLieb

variable {S E : Type*} (A : StateModel S E)

/-- **Covariance of the constrained search under a bijection** (survey item C20; lines 6814,
6938–6939, 7446–7454 of `qedft.tex`).  If a bijection `T` of the states acts on the density
variable through a bijection `τ` and shifts the energy by a function `ℓ` of the density variable,
then `F_LL(τ d) = F_LL(d) + ℓ(d)`.  With `ℓ(ρ, j) = ∫ j·∇S + ½∫ρ|∇S|²` this is the phase
covariance `F(ρ, j + ρ∇S) = F(ρ, j) + ∫ j·∇S + ½∫ρ|∇S|²`. -/
theorem search_covariance (T : S ≃ S) (τ : E ≃ E) (ℓ : E → ℝ)
    (hdens : ∀ s, A.density (T s) = τ (A.density s))
    (henergy : ∀ s, A.energy (T s) = A.energy s + ℓ (A.density s)) (d : E) :
    search A (τ d) = search A d + ((ℓ d : ℝ) : EReal) := by
  apply le_antisymm
  · refine (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).1 ?_
    refine le_iInf₂ fun s hs => ?_
    refine (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).2 ?_
    have h1 : A.density (T s) = τ d := by rw [hdens, hs]
    calc search A (τ d) ≤ (A.energy (T s) : EReal) := search_le A h1
      _ = (A.energy s : EReal) + ((ℓ d : ℝ) : EReal) := by rw [henergy, hs, EReal.coe_add]
  · refine le_iInf₂ fun s' hs' => ?_
    have h1 : A.density (T.symm s') = d := by
      apply τ.injective
      rw [← hdens, Equiv.apply_symm_apply, hs']
    have h2 : A.energy s' = A.energy (T.symm s') + ℓ d := by
      rw [← h1, ← henergy, Equiv.apply_symm_apply]
    rw [h2, EReal.coe_add]
    exact add_le_add (search_le A h1) le_rfl

/-- Invariance (Appendix A.1, translations and orthogonal transformations): a symmetry of the
internal energy that acts on density–current pairs through `τ` leaves `F_LL` invariant,
`F_LL ∘ τ = F_LL`. -/
theorem search_invariance (T : S ≃ S) (τ : E ≃ E)
    (hdens : ∀ s, A.density (T s) = τ (A.density s)) (henergy : ∀ s, A.energy (T s) = A.energy s) (d : E) :
    search A (τ d) = search A d := by
  have h := search_covariance A T τ (fun _ => 0) hdens (fun s => by simp [henergy]) d
  simpa using h

end LevyLieb

section Lieb

variable {S E V : Type*}
variable (A : StateModel S E) (B : V → E → ℝ)

/-- The ground-state energy transforms contravariantly: if `F_LL(τ d) = F_LL(d) + ⟨u₀, d⟩` and
`σ` is the induced map on potentials, `⟨σ u, d⟩ = ⟨u₀, d⟩ + ⟨u, τ d⟩`, then `Ē(σ u) = Ē(u)`.
(For the gauge transformation this is eq. `H-gauge`: `H^{v,A}` and `H^{v, A - ∇g}` are unitarily
equivalent.) -/
theorem ground_covariance (τ : E ≃ E) (σ : V → V) (u₀ : V)
    (hσ : ∀ u d, B (σ u) d = B u₀ d + B u (τ d))
    (hcov : ∀ d, search A (τ d) = search A d + ((B u₀ d : ℝ) : EReal)) (u : V) :
    ground A B (σ u) = ground A B u := by
  rw [density_variational_principle, density_variational_principle]
  rw [← τ.iInf_comp (g := fun d' => search A d' + ((B u d' : ℝ) : EReal))]
  refine iInf_congr fun d => ?_
  rw [hcov, hσ, EReal.coe_add, add_assoc]

/-- **The covariance passes from `F_LL` to the Lieb functional `F_L`** without any appeal to the
convex envelope (survey item C21; eq. `dipole-general-phase-covariance` is stated for
`F_{L,0}`): `F_L(τ d) = F_L(d) + ⟨u₀, d⟩`. -/
theorem lieb_covariance (τ : E ≃ E) (σ : V ≃ V) (u₀ : V)
    (hσ : ∀ u d, B (σ u) d = B u₀ d + B u (τ d))
    (hcov : ∀ d, search A (τ d) = search A d + ((B u₀ d : ℝ) : EReal)) (d : E) :
    lieb A B (τ d) = lieb A B d + ((B u₀ d : ℝ) : EReal) := by
  have key : ∀ u, ground A B (σ u) - ((B (σ u) d : ℝ) : EReal)
      + ((B u₀ d : ℝ) : EReal) = ground A B u - ((B u (τ d) : ℝ) : EReal) := by
    intro u
    rw [ground_covariance A B τ σ u₀ hσ hcov u, hσ]
    generalize ground A B u = G
    induction G with
    | bot => simp
    | top => rw [EReal.top_sub_coe, EReal.top_sub_coe, EReal.top_add_coe]
    | coe g =>
      rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_eq_coe_iff]; ring
  apply le_antisymm
  · refine iSup_le fun u => ?_
    rw [← key u]
    exact add_le_add (potential_lower_bound A B (σ u) d) le_rfl
  · refine EReal.add_le_of_le_sub ?_
    refine iSup_le fun u' => ?_
    refine (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).2 ?_
    obtain ⟨u, rfl⟩ := σ.surjective u'
    rw [key u]
    exact potential_lower_bound A B u (τ d)

end Lieb

section HilbertIdentities

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The exact gauge kinetic-energy increment in one coordinate direction. -/
theorem gauge_energy (u ψ : H) (h : ℝ) :
    (1 / 2 : ℝ) * ‖u + (h : ℂ) • ψ‖ ^ 2 =
      ‖u‖ ^ 2 / 2 + h * (inner ℂ u ψ).re + h ^ 2 * ‖ψ‖ ^ 2 / 2 := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right]
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    RCLike.re_to_complex]
  ring

/-- Gauge current shift, before integrating over the electronic coordinates. -/
theorem gauge_current (u ψ : H) (h : ℝ) :
    (inner ℂ ψ (u + (h : ℂ) • ψ)).re =
      (inner ℂ ψ u).re + h * ‖ψ‖ ^ 2 := by
  rw [inner_add_right, inner_smul_right, Complex.add_re, Complex.re_ofReal_mul]
  have hh := inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  simp only [RCLike.re_to_complex] at hh
  rw [hh]

/-- The simultaneous vector-potential shift preserves physical current. -/
theorem physical_current_invariant (j ρ h A : ℝ) :
    (j + ρ * h) + ρ * (A - h) = j + ρ * A := by ring

/-- Gauge cancellation also occurs directly in the covariant derivative. -/
theorem gauge_derivative_cancel (u ψ : H) (h A : ℝ) :
    (u + (h : ℂ) • ψ) + ((A - h : ℝ) : ℂ) • ψ = u + (A : ℂ) • ψ := by
  push_cast
  simp only [sub_smul]
  abel

/-- The Weyl radiation and photon-number bounds both follow from the same
weighted-annihilation shift, with weights ω and 1 respectively. -/
theorem weyl_form_norm_bound (U : H →ₗᵢ[ℂ] H) (r z : H) (a b : ℝ)
    (hz : ‖z‖ = a * b) : ‖U (r + z)‖ ≤ ‖r‖ + a * b := by
  rw [U.norm_map]
  simpa only [hz] using norm_add_le r z

/-- Polarization of the weighted-annihilation shift gives the radiation form. -/
theorem weyl_form_shift (U : H →ₗᵢ[ℂ] H) (r z s w : H) :
    inner ℂ (U (r + z)) (U (s + w)) =
      inner ℂ r s + inner ℂ z s + inner ℂ r w + inner ℂ z w := by
  rw [U.inner_map_map]
  simp only [inner_add_left, inner_add_right]
  ring

/-- Expanding the Weyl kinetic displacement gives the manuscript's signs. -/
theorem weyl_kinetic_shift (u ψ : H) (e t c : ℝ) :
    (1 / 2 : ℝ) * ‖u - ((e * t * c : ℝ) : ℂ) • ψ‖ ^ 2 =
      ‖u‖ ^ 2 / 2 - e * t * c * (inner ℂ u ψ).re +
        e ^ 2 * t ^ 2 * c ^ 2 * ‖ψ‖ ^ 2 / 2 := by
  have hh := gauge_energy u ψ (-(e * t * c))
  simp only [Complex.ofReal_neg, neg_smul, ← sub_eq_add_neg] at hh
  rw [hh]
  ring

/-- Adding the exact radiation shift and the kinetic shift gives
`weyl-PF-energy-shift`, including its quadratic coefficient. -/
theorem weyl_pf_energy (E rad field J C e t a : ℝ) :
    (E - rad - e * t * J + e ^ 2 * t ^ 2 * C / 2) +
      (rad + t * field + t ^ 2 * a) =
      E + t * (field - e * J) + t ^ 2 * (a + e ^ 2 * C / 2) := by ring

/-- The dipole self-polarization term completes the square and ensures
nonnegativity together with the corresponding linear field term. -/
theorem completed_radiation_square (r z : H) :
    0 ≤ ‖r‖ ^ 2 + 2 * (inner ℂ r z).re + ‖z‖ ^ 2 := by
  have he := norm_add_sq (𝕜 := ℂ) r z
  simp only [RCLike.re_to_complex] at he
  rw [← he]
  positivity

/-- The quadratic/linear dilation powers have equivalent nonnegative forms. -/
theorem dilation_form_comparison (l K C R : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    min (l ^ 2) l * (K + C + R) ≤ l ^ 2 * K + l * C + l * R ∧
      l ^ 2 * K + l * C + l * R ≤ max (l ^ 2) l * (K + C + R) := by
  have h1 := mul_le_mul_of_nonneg_right (min_le_left (l ^ 2) l) hK
  have h2 := mul_le_mul_of_nonneg_right (min_le_right (l ^ 2) l) hC
  have h3 := mul_le_mul_of_nonneg_right (min_le_right (l ^ 2) l) hR
  have h4 := mul_le_mul_of_nonneg_right (le_max_left (l ^ 2) l) hK
  have h5 := mul_le_mul_of_nonneg_right (le_max_right (l ^ 2) l) hC
  have h6 := mul_le_mul_of_nonneg_right (le_max_right (l ^ 2) l) hR
  constructor <;> nlinarith

/-- Dilation of a covariant derivative produces its exact quadratic weight. -/
theorem dilation_kinetic (U : H →ₗᵢ[ℂ] H) (u : H) (l : ℝ) :
    ‖(l : ℂ) • U u‖ ^ 2 = l ^ 2 * ‖u‖ ^ 2 := by
  simp [norm_smul, mul_pow, sq_abs]

/-- The Gram quadratic form in the PZW self-polarization term is a norm. -/
theorem gram_quadratic_form {ι : Type*} [Fintype ι] (g : ι → H) (c : ι → ℝ) :
    ‖∑ i, (c i : ℂ) • g i‖ ^ 2 =
      ∑ i, ∑ j, c i * c j * (inner ℂ (g i) (g j)).re := by
  have hh := (inner_self_eq_norm_sq (𝕜 := ℂ) (∑ i, (c i : ℂ) • g i)).symm
  simp only [RCLike.re_to_complex] at hh
  rw [hh]
  simp only [sum_inner, inner_sum, Complex.re_sum, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, Complex.re_ofReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs := inner_re_symm (𝕜 := ℂ) (g j) (g i)
  simp only [RCLike.re_to_complex] at hs
  rw [hs]
  ring

/-- A coherent derivative's connection follows from the annihilation
expectation. The norm identity below needs the second, CCR norm identity. -/
theorem coherent_derivative_connection (z a : H) (c : ℂ)
    (hz : ‖z‖ = 1) (hza : inner ℂ z a = c) :
    inner ℂ z (a - (c.re : ℂ) • z) = Complex.I * (c.im : ℂ) := by
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hz, hza]
  apply Complex.ext <;> simp

/-- The algebraic CCR calculation in `weyl-coherent-metric`. -/
theorem coherent_derivative_metric (z a : H) (c : ℂ) (r : ℝ)
    (hz : ‖z‖ = 1) (hza : inner ℂ z a = c)
    (ha : ‖a‖ ^ 2 = r + ‖c‖ ^ 2) :
    ‖a - (c.re : ℂ) • z‖ ^ 2 = r + c.im ^ 2 := by
  have hre : (inner ℂ a z).re = c.re := by
    have hh := inner_re_symm (𝕜 := ℂ) a z
    simpa only [RCLike.re_to_complex, hza] using hh
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right]
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
  simp only [RCLike.re_to_complex, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, hz, one_pow, mul_one, hre, ha, Complex.sq_norm,
    Complex.normSq_apply]
  ring

/-- Adding the scalar phase changes the Berry connection by its gradient. -/
theorem coherent_phase_connection (z d : H) (s b : ℝ)
    (hz : ‖z‖ = 1) (hzd : inner ℂ z d = Complex.I * (b : ℂ)) :
    inner ℂ z (d + (Complex.I * (s : ℂ)) • z) =
      Complex.I * ((s + b : ℝ) : ℂ) := by
  rw [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hz, hzd]
  push_cast
  ring

/-- Completing the phase square yields the precise coherent metric formula. -/
theorem coherent_phase_metric (z d : H) (s b r : ℝ)
    (hz : ‖z‖ = 1) (hzd : inner ℂ z d = Complex.I * (b : ℂ))
    (hd : ‖d‖ ^ 2 = r + b ^ 2) :
    ‖d + (Complex.I * (s : ℂ)) • z‖ ^ 2 = r + (s + b) ^ 2 := by
  have hdz : inner ℂ d z = -(Complex.I * (b : ℂ)) := by
    rw [← inner_conj_symm, hzd]
    simp
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, hdz]
  simp only [RCLike.re_to_complex, norm_smul, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, hz, one_mul, mul_one, sq_abs,
    hd, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im]
  ring

/-- The Lipschitz estimate on the real subspace reduces to exp(x) ≥ 1+x. -/
theorem real_coherent_lipschitz_scalar (d : ℝ) :
    2 * (1 - Real.exp (-d ^ 2 / 2)) ≤ d ^ 2 := by
  have he := Real.add_one_le_exp (-d ^ 2 / 2)
  linarith

end HilbertIdentities

end GptLean.Transformations
