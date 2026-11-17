import GptLean.PhysicalWeylRadiation
import GptLean.PhysicalPFSoftTag

/-!
The photon displacement `W(f)` on the Pauli--Fierz reference domain
(`cor-weyl-PF-shifts` for vectors).

`W(f)` acts at every configuration point. On the radiation graph it is the
operator of `PhysicalWeylRadiation`, so the fiber map of `PhysicalPFFiberMap`
lifts it to the reference domain. Write `u` for a reference vector,
`a_K u` for the annihilation by the weighted kernel `K = (ω f, √ω f)`, and
`c_b(x) = 2 Re ⟨κ_b(x), f⟩` for the classical field of `f` at the kernel of the
coordinate `b`. Then:

* the wave function, the Coulomb term and the ordinary derivatives are moved
  by the isometry `W(f)`, so their norms are unchanged;
* `‖√H_rad W u‖² = ‖√H_rad u‖² + 2 Re ⟨a_K u, u⟩ + ‖√ω f‖² ‖u‖²`;
* the field shifts by the classical field, `A_b W u = W (A_b u + c_b u)`, hence
  the covariant derivative shifts by `D_b W u = W (D_b u - e c_b u)`;
* `‖D_b W u‖² = ‖D_b u‖² - 2e ∫ c_b Re ⟨D_b u, u⟩ + e² ∫ c_b² |u|²`.

For a real direction, `c_b = 0` for every coordinate, the kinetic energy is
unchanged and `E(W u) = E(u) + 2 Re ⟨a_K u, u⟩ + ‖√ω f‖² ‖u‖²`.
-/

noncomputable section

namespace GptLean.PhysicalWeyl

open MeasureTheory Filter PhysicalFock PhysicalPFReference PhysicalPFSoftTag
  PhysicalPFVacuumEnergy Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section L2

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_eq_of_ae (F G : Lp H 2 μ) (h : ∀ᵐ x ∂μ, ‖F x‖ = ‖G x‖) : ‖F‖ = ‖G‖ := by
  have h2 : ‖F‖ ^ 2 = ‖G‖ ^ 2 := by
    rw [norm_sq_eq_integral F, norm_sq_eq_integral G]
    apply integral_congr_ae
    filter_upwards [h] with x hx
    rw [hx]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

theorem integral_re_inner (B U : Lp H 2 μ) :
    ∫ x, (⟪B x, U x⟫_ℂ).re ∂μ = (⟪B, U⟫_ℂ).re := by
  rw [L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) B U)

/-- An a.e. quadratic identity integrates to the corresponding norm identity. -/
theorem norm_sq_of_ae (R A B U : Lp H 2 μ) (c : ℝ)
    (h : ∀ᵐ x ∂μ, ‖R x‖ ^ 2 = ‖A x‖ ^ 2 + 2 * (⟪B x, U x⟫_ℂ).re + c * ‖U x‖ ^ 2) :
    ‖R‖ ^ 2 = ‖A‖ ^ 2 + 2 * (⟪B, U⟫_ℂ).re + c * ‖U‖ ^ 2 := by
  have hA : Integrable (fun x => ‖A x‖ ^ 2) μ := integrable_norm_sq A
  have hBU : Integrable (fun x => 2 * (⟪B x, U x⟫_ℂ).re) μ :=
    (L2.integrable_inner (𝕜 := ℂ) B U).re.const_mul 2
  have hAB : Integrable (fun x => ‖A x‖ ^ 2 + 2 * (⟪B x, U x⟫_ℂ).re) μ := hA.add hBU
  have hcU : Integrable (fun x => c * ‖U x‖ ^ 2) μ := (integrable_norm_sq U).const_mul c
  calc ‖R‖ ^ 2 = ∫ x, ‖R x‖ ^ 2 ∂μ := norm_sq_eq_integral R
    _ = ∫ x, (‖A x‖ ^ 2 + 2 * (⟪B x, U x⟫_ℂ).re + c * ‖U x‖ ^ 2) ∂μ := integral_congr_ae h
    _ = (∫ x, ‖A x‖ ^ 2 ∂μ + ∫ x, 2 * (⟪B x, U x⟫_ℂ).re ∂μ) + ∫ x, c * ‖U x‖ ^ 2 ∂μ := by
        rw [integral_add hAB hcU, integral_add hA hBU]
    _ = ‖A‖ ^ 2 + 2 * (⟪B, U⟫_ℂ).re + c * ‖U‖ ^ 2 := by
        rw [integral_const_mul, integral_const_mul, integral_re_inner, ← norm_sq_eq_integral A,
          ← norm_sq_eq_integral U]

theorem norm_sub_real_smul_sq' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (D U : E) (r : ℝ) :
    ‖D - (r : ℂ) • U‖ ^ 2 = ‖D‖ ^ 2 - 2 * (r * (⟪D, U⟫_ℂ).re) + r ^ 2 * ‖U‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, RCLike.re_to_complex, Complex.re_ofReal_mul]

/-- **Kinetic shift by a bounded real field**, integrated. -/
theorem norm_sq_shift_ae (R D U : Lp H 2 μ) (c : X → ℝ) (hcm : AEStronglyMeasurable c μ) (B : ℝ)
    (hcb : ∀ᵐ x ∂μ, ‖c x‖ ≤ B) (e : ℝ)
    (h : ∀ᵐ x ∂μ, ‖R x‖ = ‖D x - ((e * c x : ℝ) : ℂ) • U x‖) :
    ‖R‖ ^ 2 = ‖D‖ ^ 2 - 2 * e * ∫ x, c x * (⟪D x, U x⟫_ℂ).re ∂μ +
      e ^ 2 * ∫ x, c x ^ 2 * ‖U x‖ ^ 2 ∂μ := by
  have hD : Integrable (fun x => ‖D x‖ ^ 2) μ := integrable_norm_sq D
  have hre : Integrable (fun x => (⟪D x, U x⟫_ℂ).re) μ := (L2.integrable_inner (𝕜 := ℂ) D U).re
  have h1 : Integrable (fun x => c x * (⟪D x, U x⟫_ℂ).re) μ := hre.bdd_mul hcm hcb
  have h2 : Integrable (fun x => c x ^ 2 * ‖U x‖ ^ 2) μ :=
    (integrable_norm_sq U).bdd_mul (hcm.pow 2) (c := B ^ 2) (hcb.mono fun x hx => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2)
  have h1' : Integrable (fun x => 2 * e * (c x * (⟪D x, U x⟫_ℂ).re)) μ := h1.const_mul _
  have h2' : Integrable (fun x => e ^ 2 * (c x ^ 2 * ‖U x‖ ^ 2)) μ := h2.const_mul _
  have hDs : Integrable (fun x => ‖D x‖ ^ 2 - 2 * e * (c x * (⟪D x, U x⟫_ℂ).re)) μ :=
    hD.sub h1'
  calc ‖R‖ ^ 2 = ∫ x, ‖R x‖ ^ 2 ∂μ := norm_sq_eq_integral R
    _ = ∫ x, (‖D x‖ ^ 2 - 2 * e * (c x * (⟪D x, U x⟫_ℂ).re) +
          e ^ 2 * (c x ^ 2 * ‖U x‖ ^ 2)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [h] with x hx
        rw [hx, norm_sub_real_smul_sq']
        ring
    _ = (∫ x, ‖D x‖ ^ 2 ∂μ - ∫ x, 2 * e * (c x * (⟪D x, U x⟫_ℂ).re) ∂μ) +
          ∫ x, e ^ 2 * (c x ^ 2 * ‖U x‖ ^ 2) ∂μ := by
        rw [integral_add hDs h2', integral_sub hD h1']
    _ = _ := by rw [integral_const_mul, integral_const_mul, ← norm_sq_eq_integral D]

theorem norm_le_of_ae_le (F G : Lp H 2 μ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ᵐ x ∂μ, ‖F x‖ ≤ c * ‖G x‖) : ‖F‖ ≤ c * ‖G‖ := by
  have h2 : ‖F‖ ^ 2 ≤ (c * ‖G‖) ^ 2 := by
    rw [norm_sq_eq_integral F, mul_pow, norm_sq_eq_integral G, ← integral_const_mul]
    refine integral_mono_ae (integrable_norm_sq F) ((integrable_norm_sq G).const_mul _) ?_
    filter_upwards [h] with x hx
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

theorem norm_sq_le_two_of_ae (F G U : Lp H 2 μ) (c : ℝ)
    (h : ∀ᵐ x ∂μ, ‖F x‖ ^ 2 ≤ 2 * ‖G x‖ ^ 2 + 2 * c ^ 2 * ‖U x‖ ^ 2) :
    ‖F‖ ^ 2 ≤ 2 * ‖G‖ ^ 2 + 2 * c ^ 2 * ‖U‖ ^ 2 := by
  have hG : Integrable (fun x => 2 * ‖G x‖ ^ 2) μ := (integrable_norm_sq G).const_mul 2
  have hU : Integrable (fun x => 2 * c ^ 2 * ‖U x‖ ^ 2) μ := (integrable_norm_sq U).const_mul _
  calc ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂μ := norm_sq_eq_integral F
    _ ≤ ∫ x, (2 * ‖G x‖ ^ 2 + 2 * c ^ 2 * ‖U x‖ ^ 2) ∂μ :=
        integral_mono_ae (integrable_norm_sq F) (hG.add hU) h
    _ = ∫ x, 2 * ‖G x‖ ^ 2 ∂μ + ∫ x, 2 * c ^ 2 * ‖U x‖ ^ 2 ∂μ := integral_add hG hU
    _ = _ := by rw [integral_const_mul, integral_const_mul, ← norm_sq_eq_integral G,
          ← norm_sq_eq_integral U]

end L2

theorem norm_sub_smul_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (D u : E) {r B : ℝ} (hr : |r| ≤ B) :
    ‖D - (r : ℂ) • u‖ ^ 2 ≤ 2 * ‖D‖ ^ 2 + 2 * B ^ 2 * ‖u‖ ^ 2 := by
  have h := norm_sub_le D ((r : ℂ) • u)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs] at h
  have hB : |r| * ‖u‖ ≤ B * ‖u‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
  have h2 : ‖D - (r : ℂ) • u‖ ≤ ‖D‖ + B * ‖u‖ := h.trans (by linarith)
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith [sq_nonneg (‖D‖ - B * ‖u‖)]

theorem abs_mul_le_of_norm_le {e c B : ℝ} (hc : ‖c‖ ≤ B) : |e * c| ≤ |e| * B := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by rwa [Real.norm_eq_abs] at hc) (abs_nonneg e)

theorem sum_le_two_mul_add {ι : Type*} [Fintype ι] (x y : ι → ℝ) (c : ℝ)
    (h : ∀ b, y b ≤ 2 * x b + c) : ∑ b, y b ≤ 2 * ∑ b, x b + Fintype.card ι * c := by
  calc ∑ b, y b ≤ ∑ b, (2 * x b + c) := Finset.sum_le_sum fun b _ => h b
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]

theorem energy_bound_combine {S S' R R' P P' X T : ℝ} (hS : S' ≤ 2 * S + T) (hR : R' ≤ 2 * R + X)
    (hP : P' = P) (hP0 : 0 ≤ P) :
    (1 / 2 : ℝ) * S' + R' + P' ≤ 2 * ((1 / 2 : ℝ) * S + R + P) + (T / 2 + X) := by
  subst hP
  linarith

theorem norm_shift_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (L : E ≃ₗᵢ[ℂ] E) (D U : E) {r : ℝ} (hr : r = 0) : ‖L (D - (r : ℂ) • U)‖ = ‖D‖ := by
  rw [LinearIsometryEquiv.norm_map, hr, Complex.ofReal_zero, zero_smul, sub_zero]

theorem norm_sub_real_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (D U : E) (r : ℝ) :
    ‖D - (r : ℂ) • U‖ ^ 2 = ‖D‖ ^ 2 - 2 * (r * (⟪D, U⟫_ℂ).re) + r ^ 2 * ‖U‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, RCLike.re_to_complex, Complex.re_ofReal_mul]

theorem quad_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (c : ℝ)
    {a a' b b' u u' : E} (ha : a = a') (hb : b = b') (hu : u = u') :
    ‖a‖ ^ 2 + 2 * (⟪b, u⟫_ℂ).re + c * ‖u‖ ^ 2 = ‖a'‖ ^ 2 + 2 * (⟪b', u'⟫_ℂ).re + c * ‖u'‖ ^ 2 := by
  subst ha hb hu
  rfl

theorem energy_combine {k k' r r' p p' X Y : ℝ} (hk : k' = k) (hr : r' = r + X + Y)
    (hp : p' = p) : k' + r' + p' = (k + r + p) + X + Y := by
  subst hk hr hp
  ring

theorem energy_combine' {k k' r r' p p' X Y Z : ℝ} (hk : k' = k + Z) (hr : r' = r + X + Y)
    (hp : p' = p) : k' + r' + p' = (k + r + p) + X + Y + Z := by
  subst hk hr hp
  ring

theorem half_sum_shift {ι : Type*} (s : Finset ι) (x y t : ι → ℝ)
    (h : ∀ b ∈ s, y b = x b + t b) :
    (1 / 2 : ℝ) * ∑ b ∈ s, y b = (1 / 2 : ℝ) * ∑ b ∈ s, x b + (1 / 2 : ℝ) * ∑ b ∈ s, t b := by
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, mul_add]

theorem weyl_covariant_algebra {E : Type*} [AddCommGroup E] [Module ℂ E] (L : E →ₗ[ℂ] E)
    (o A u : E) (e c : ℝ) :
    (-Complex.I) • L o - (e : ℂ) • L (A + (c : ℂ) • u) =
      L (((-Complex.I) • o - (e : ℂ) • A) - ((e * c : ℝ) : ℂ) • u) := by
  simp only [map_sub, map_add, map_smul, smul_add, Complex.ofReal_mul, mul_smul]
  abel

variable {I : Type} [Fintype I] [DecidableEq I] (V : Position I → ℝ)
  (W : ConcreteWeylLaw photonMeasure) {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
  (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)

/-- `W(f)` as a bounded operator on the photon Fock space. -/
abbrev weylOp (W : ConcreteWeylLaw photonMeasure) (f : Lp ℂ 2 photonMeasure) :
    PhotonFock →L[ℂ] PhotonFock :=
  (W.weyl f).toLinearIsometry.toContinuousLinearMap

/-- **`W(f)` on the reference domain.** -/
def weylRef : Reference I V →L[ℂ] Reference I V :=
  PhysicalPFFiberMap.map V (weylOp W f) (weylGraph W K hK) (weylGraph_inclusion W K hK)

theorem inclusion_weylRef (u : Reference I V) :
    inclusion I V (weylRef V W K hK u) = (weylOp W f).compLpL 2 volume (inclusion I V u) := rfl

theorem inclusion_weylRef_ae (u : Reference I V) :
    ∀ᵐ x ∂volume, inclusion I V (weylRef V W K hK u) x = W.weyl f (inclusion I V u x) :=
  (weylOp W f).coeFn_compLpL (inclusion I V u)

theorem ordinary_weylRef_ae (i : I) (u : Reference I V) :
    ∀ᵐ x ∂volume, ordinary I V i (weylRef V W K hK u) x = W.weyl f (ordinary I V i u x) :=
  (weylOp W f).coeFn_compLpL (ordinary I V i u)

theorem radiationSource_weylRef_ae (u : Reference I V) :
    ∀ᵐ x ∂volume, radiationSource I V (weylRef V W K hK u) x =
      weylGraph W K hK (radiationSource I V u x) :=
  (weylGraph W K hK).coeFn_compLpL (radiationSource I V u)

theorem potential_weylRef_ae (u : Reference I V) :
    ∀ᵐ x ∂volume, potential I V (weylRef V W K hK u) x = W.weyl f (potential I V u x) :=
  (weylOp W f).coeFn_compLpL (potential I V u)

theorem inclusion_weylRef_norm (u : Reference I V) :
    ‖inclusion I V (weylRef V W K hK u)‖ = ‖inclusion I V u‖ :=
  norm_eq_of_ae _ _ ((inclusion_weylRef_ae V W K hK u).mono fun _ hx =>
    (congrArg norm hx).trans (LinearIsometryEquiv.norm_map _ _))

theorem potential_weylRef_norm (u : Reference I V) :
    ‖potential I V (weylRef V W K hK u)‖ = ‖potential I V u‖ :=
  norm_eq_of_ae _ _ ((potential_weylRef_ae V W K hK u).mono fun _ hx =>
    (congrArg norm hx).trans (LinearIsometryEquiv.norm_map _ _))

theorem inclusion_weylRef_fermionic {N : ℕ} {V' : Position (Fin N × Fin 3) → ℝ}
    (u : Reference (Fin N × Fin 3) V')
    (hu : inclusion (Fin N × Fin 3) V' u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    inclusion (Fin N × Fin 3) V' (weylRef V' W K hK u) ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
  (PhysicalElectronicFermions.mem_fermionicSubspace_iff N PhotonFock _).mpr
    (PhysicalElectronicFermions.fiberOperator_character N PhotonFock (weylOp W f) _
      ((PhysicalElectronicFermions.mem_fermionicSubspace_iff N PhotonFock _).mp hu))

/-- The annihilation `a(ω f)` of a reference vector. -/
def annihilationRef (u : Reference I V) : WaveSpace I :=
  (kernelAnnihilation K).compLpL 2 volume (radiationSource I V u)

/-- **Radiation energy of the displaced vector**,
`‖√H_rad W u‖² = ‖√H_rad u‖² + 2 Re ⟨a_K u, u⟩ + ‖√ω f‖² ‖u‖²`. -/
theorem radiation_weylRef_norm_sq (u : Reference I V) :
    ‖radiation I V (weylRef V W K hK u)‖ ^ 2 =
      ‖radiation I V u‖ ^ 2 + 2 * (⟪annihilationRef V K u, inclusion I V u⟫_ℂ).re +
        ‖K.val.2‖ ^ 2 * ‖inclusion I V u‖ ^ 2 := by
  apply norm_sq_of_ae
  filter_upwards [radiation_ae V (weylRef V W K hK u), radiationSource_weylRef_ae V W K hK u,
    radiation_ae V u, (kernelAnnihilation K).coeFn_compLpL (radiationSource I V u),
    reference_radiation_ae I V u] with x h₁ h₂ h₃ h₄ h₅
  have hd : radiation I V (weylRef V W K hK u) x =
      radiationGraphDerivative (weylGraph W K hK (radiationSource I V u x)) :=
    h₁.trans (congrArg radiationGraphDerivative h₂)
  have h₄' : annihilationRef V K u x = kernelAnnihilation K (radiationSource I V u x) := h₄
  exact (congrArg (fun z : PhotonFock => ‖z‖ ^ 2) hd).trans
    ((weylGraph_derivative_norm_sq W K hK (radiationSource I V u x)).trans
      (quad_congr _ h₃.symm h₄'.symm h₅.symm))

section Field

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)

/-- The classical field `c_b(x) = 2 Re ⟨κ_b(x), f⟩` of the displacement. -/
def classicalField (f : Lp ℂ 2 photonMeasure) (b : I) (x : Position I) : ℝ :=
  2 * (⟪(κ b x).val.1, f⟫_ℂ).re

omit [DecidableEq I] in
include hκ in
theorem classicalField_aestronglyMeasurable (f : Lp ℂ 2 photonMeasure) (b : I) :
    AEStronglyMeasurable (classicalField κ f b) volume := by
  have hc : Continuous (fun k : WeightedPhotonKernel => 2 * (⟪k.val.1, f⟫_ℂ).re) :=
    continuous_const.mul (Complex.continuous_re.comp
      ((continuous_fst.comp continuous_subtype_val).inner continuous_const))
  exact hc.comp_aestronglyMeasurable (hκ b)

omit [DecidableEq I] in
include hbound in
theorem classicalField_bound (f : Lp ℂ 2 photonMeasure) (b : I) :
    ∀ᵐ x ∂volume, ‖classicalField κ f b x‖ ≤ 2 * M * ‖f‖ := by
  filter_upwards [hbound b] with x hx
  unfold classicalField
  rw [Real.norm_eq_abs, abs_mul, abs_two]
  have h1 : |(⟪(κ b x).val.1, f⟫_ℂ).re| ≤ ‖(κ b x).val.1‖ * ‖f‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have h2 : ‖(κ b x).val.1‖ ≤ M := (norm_fst_le (κ b x).val).trans hx
  nlinarith [norm_nonneg f, norm_nonneg (κ b x).val.1]

/-- **The field shifts by the classical field.** -/
theorem field_weylRef_ae (b : I) (u : Reference I V) :
    ∀ᵐ x ∂volume, field I V C κ hκ M hbound b (weylRef V W K hK u) x =
      W.weyl f (field I V C κ hκ M hbound b u x +
        (classicalField κ f b x : ℂ) • inclusion I V u x) := by
  filter_upwards [field_ae V C (weylRef V W K hK u) κ hκ M hbound b,
    radiationSource_weylRef_ae V W K hK u, field_ae V C u κ hκ M hbound b,
    reference_radiation_ae I V u] with x h₁ h₂ h₃ h₄
  exact h₁.trans ((congrArg (kernelField C (κ b x)) h₂).trans
    ((kernelField_weylGraph W K hK C (κ b x) (radiationSource I V u x)).trans
      (congrArg (W.weyl f) (congrArg₂
        (fun a z => a + ((2 * (⟪(κ b x).val.1, f⟫_ℂ).re : ℝ) : ℂ) • z) h₃.symm h₄.symm))))

/-- **The covariant derivative shifts by the classical field.** -/
theorem covariant_weylRef_ae (e : ℝ) (b : I) (u : Reference I V) :
    ∀ᵐ x ∂volume, covariant I V C κ hκ M hbound e b (weylRef V W K hK u) x =
      W.weyl f (covariant I V C κ hκ M hbound e b u x -
        ((e * classicalField κ f b x : ℝ) : ℂ) • inclusion I V u x) := by
  filter_upwards [covariant_ae V C (weylRef V W K hK u) κ hκ M hbound e b,
    ordinary_weylRef_ae V W K hK b u, field_weylRef_ae V W K hK C κ hκ M hbound b u,
    covariant_ae V C u κ hκ M hbound e b] with x h₁ h₂ h₃ h₄
  exact h₁.trans ((congrArg₂ (fun a z => (-Complex.I) • a - (e : ℂ) • z) h₂ h₃).trans
    ((weyl_covariant_algebra (W.weyl f).toLinearEquiv.toLinearMap (ordinary I V b u x)
      (field I V C κ hκ M hbound b u x) (inclusion I V u x) e (classicalField κ f b x)).trans
      (congrArg (fun z => W.weyl f (z - ((e * classicalField κ f b x : ℝ) : ℂ) •
        inclusion I V u x)) h₄.symm)))

/-- **Kinetic shift**, `‖D_b W u‖² = ‖D_b u‖² - 2e ∫ c_b Re ⟨D_b u, u⟩ + e² ∫ c_b² |u|²`. -/
theorem covariant_weylRef_norm_sq (e : ℝ) (b : I) (u : Reference I V) :
    ‖covariant I V C κ hκ M hbound e b (weylRef V W K hK u)‖ ^ 2 =
      ‖covariant I V C κ hκ M hbound e b u‖ ^ 2 -
        2 * e * (∫ x, classicalField κ f b x *
          (⟪covariant I V C κ hκ M hbound e b u x, inclusion I V u x⟫_ℂ).re) +
        e ^ 2 * (∫ x, classicalField κ f b x ^ 2 * ‖inclusion I V u x‖ ^ 2) := by
  apply norm_sq_shift_ae _ _ _ (classicalField κ f b)
    (classicalField_aestronglyMeasurable κ hκ f b) _ (classicalField_bound κ M hbound f b) e
  filter_upwards [covariant_weylRef_ae V W K hK C κ hκ M hbound e b u] with x hx
  exact (congrArg norm hx).trans (LinearIsometryEquiv.norm_map _ _)

/-- For a real direction the covariant derivative keeps its norm. -/
theorem covariant_weylRef_norm_of_real (e : ℝ) (b : I)
    (hreal : ∀ᵐ x ∂volume, classicalField κ f b x = 0) (u : Reference I V) :
    ‖covariant I V C κ hκ M hbound e b (weylRef V W K hK u)‖ =
      ‖covariant I V C κ hκ M hbound e b u‖ := by
  apply norm_eq_of_ae
  filter_upwards [covariant_weylRef_ae V W K hK C κ hκ M hbound e b u, hreal] with x hx hc
  exact (congrArg norm hx).trans (norm_shift_zero (W.weyl f) _ _ (by rw [hc, mul_zero]))

/-- **Energy of the displaced vector in a real direction**,
`E(W u) = E(u) + 2 Re ⟨a_K u, u⟩ + ‖√ω f‖² ‖u‖²`. -/
theorem energy_weylRef_of_real (e : ℝ)
    (hreal : ∀ b, ∀ᵐ x ∂volume, classicalField κ f b x = 0) (u : Reference I V) :
    energy I V C κ hκ M hbound e (weylRef V W K hK u) =
      energy I V C κ hκ M hbound e u + 2 * (⟪annihilationRef V K u, inclusion I V u⟫_ℂ).re +
        ‖K.val.2‖ ^ 2 * ‖inclusion I V u‖ ^ 2 := by
  have hk : kineticEnergy I V C κ hκ M hbound e (weylRef V W K hK u) =
      kineticEnergy I V C κ hκ M hbound e u :=
    congrArg (fun r : ℝ => (1 / 2 : ℝ) * r) (Finset.sum_congr rfl fun b _ =>
      congrArg (fun r : ℝ => r ^ 2)
        (covariant_weylRef_norm_of_real V W K hK C κ hκ M hbound e b (hreal b) u))
  exact energy_combine hk (radiation_weylRef_norm_sq V W K hK u)
    (congrArg (fun r : ℝ => r ^ 2) (potential_weylRef_norm V W K hK u))

/-- **Energy of the displaced vector**, general direction. -/
theorem energy_weylRef (e : ℝ) (u : Reference I V) :
    energy I V C κ hκ M hbound e (weylRef V W K hK u) =
      energy I V C κ hκ M hbound e u + 2 * (⟪annihilationRef V K u, inclusion I V u⟫_ℂ).re +
        ‖K.val.2‖ ^ 2 * ‖inclusion I V u‖ ^ 2 +
        (1 / 2 : ℝ) * ∑ b, (-(2 * e * ∫ x, classicalField κ f b x *
          (⟪covariant I V C κ hκ M hbound e b u x, inclusion I V u x⟫_ℂ).re) +
          e ^ 2 * ∫ x, classicalField κ f b x ^ 2 * ‖inclusion I V u x‖ ^ 2) := by
  have hk : kineticEnergy I V C κ hκ M hbound e (weylRef V W K hK u) =
      kineticEnergy I V C κ hκ M hbound e u +
        (1 / 2 : ℝ) * ∑ b, (-(2 * e * ∫ x, classicalField κ f b x *
          (⟪covariant I V C κ hκ M hbound e b u x, inclusion I V u x⟫_ℂ).re) +
          e ^ 2 * ∫ x, classicalField κ f b x ^ 2 * ‖inclusion I V u x‖ ^ 2) := by
    exact half_sum_shift Finset.univ
      (fun b => ‖covariant I V C κ hκ M hbound e b u‖ ^ 2)
      (fun b => ‖covariant I V C κ hκ M hbound e b (weylRef V W K hK u)‖ ^ 2)
      (fun b => -(2 * e * ∫ x, classicalField κ f b x *
          (⟪covariant I V C κ hκ M hbound e b u x, inclusion I V u x⟫_ℂ).re) +
          e ^ 2 * ∫ x, classicalField κ f b x ^ 2 * ‖inclusion I V u x‖ ^ 2)
      (fun b _ => (covariant_weylRef_norm_sq V W K hK C κ hκ M hbound e b u).trans (by ring))
  exact energy_combine' hk (radiation_weylRef_norm_sq V W K hK u)
    (congrArg (fun r : ℝ => r ^ 2) (potential_weylRef_norm V W K hK u))

theorem annihilationRef_norm_le (k : WeightedPhotonKernel) (u : Reference I V) :
    ‖annihilationRef V k u‖ ≤ ‖k.val.2‖ * ‖radiation I V u‖ := by
  apply norm_le_of_ae_le _ _ (norm_nonneg _)
  filter_upwards [(kernelAnnihilation k).coeFn_compLpL (radiationSource I V u),
    radiation_ae V u] with x h₁ h₂
  have h₁' : annihilationRef V k u x = kernelAnnihilation k (radiationSource I V u x) := h₁
  exact (congrArg norm h₁').trans_le ((kernelAnnihilation_norm_le k _).trans_eq
    (congrArg (fun z : PhotonFock => ‖k.val.2‖ * ‖z‖) h₂.symm))

theorem covariant_weylRef_norm_sq_le (e : ℝ) (b : I) (u : Reference I V) :
    ‖covariant I V C κ hκ M hbound e b (weylRef V W K hK u)‖ ^ 2 ≤
      2 * ‖covariant I V C κ hκ M hbound e b u‖ ^ 2 +
        2 * (|e| * (2 * M * ‖f‖)) ^ 2 * ‖inclusion I V u‖ ^ 2 := by
  apply norm_sq_le_two_of_ae
  filter_upwards [covariant_weylRef_ae V W K hK C κ hκ M hbound e b u,
    classicalField_bound κ M hbound f b] with x hx hc
  exact ((congrArg (fun z : PhotonFock => ‖z‖ ^ 2) hx).trans
    (congrArg (fun r : ℝ => r ^ 2) (LinearIsometryEquiv.norm_map _ _))).le.trans
      (norm_sub_smul_sq_le _ _ (abs_mul_le_of_norm_le hc))

theorem radiation_weylRef_norm_sq_le (u : Reference I V) :
    ‖radiation I V (weylRef V W K hK u)‖ ^ 2 ≤
      2 * ‖radiation I V u‖ ^ 2 + 2 * ‖K.val.2‖ ^ 2 * ‖inclusion I V u‖ ^ 2 := by
  have h1 : (⟪annihilationRef V K u, inclusion I V u⟫_ℂ).re ≤
      ‖K.val.2‖ * ‖radiation I V u‖ * ‖inclusion I V u‖ :=
    (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (annihilationRef_norm_le V K u) (norm_nonneg _)))
  refine (radiation_weylRef_norm_sq V W K hK u).trans_le ?_
  nlinarith [sq_nonneg (‖radiation I V u‖ - ‖K.val.2‖ * ‖inclusion I V u‖)]

/-- **The displaced energy is controlled by the energy and the mass.** -/
theorem energy_weylRef_le (e : ℝ) (u : Reference I V) :
    energy I V C κ hκ M hbound e (weylRef V W K hK u) ≤
      2 * energy I V C κ hκ M hbound e u +
        ((Fintype.card I * (2 * (|e| * (2 * M * ‖f‖)) ^ 2 * ‖inclusion I V u‖ ^ 2)) / 2 +
          2 * ‖K.val.2‖ ^ 2 * ‖inclusion I V u‖ ^ 2) := by
  have hsum : ∑ b, ‖covariant I V C κ hκ M hbound e b (weylRef V W K hK u)‖ ^ 2 ≤
      2 * ∑ b, ‖covariant I V C κ hκ M hbound e b u‖ ^ 2 +
        Fintype.card I * (2 * (|e| * (2 * M * ‖f‖)) ^ 2 * ‖inclusion I V u‖ ^ 2) :=
    sum_le_two_mul_add (fun b => ‖covariant I V C κ hκ M hbound e b u‖ ^ 2)
      (fun b => ‖covariant I V C κ hκ M hbound e b (weylRef V W K hK u)‖ ^ 2)
      (2 * (|e| * (2 * M * ‖f‖)) ^ 2 * ‖inclusion I V u‖ ^ 2)
      (fun b => covariant_weylRef_norm_sq_le V W K hK C κ hκ M hbound e b u)
  exact energy_bound_combine hsum (radiation_weylRef_norm_sq_le V W K hK u)
    (congrArg (fun r : ℝ => r ^ 2) (potential_weylRef_norm V W K hK u)) (sq_nonneg _)

end Field

end GptLean.PhysicalWeyl
