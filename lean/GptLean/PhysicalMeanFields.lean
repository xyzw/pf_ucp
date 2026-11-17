import GptLean.PhysicalWeylStates

/-!
`prop-optimizer-mean-fields` (ii): the mean transverse electric field of a
constrained optimizer vanishes.

Let `Γ` minimize the energy among density matrices with its density and
combined current, and let `Γ = ∑ₙ |uₙ⟩⟨uₙ|` be a spectral source. For a real
displacement direction `f`, `W(t f)` keeps the pair, and
`E(W(t f) Γ W(t f)†) = E(Γ) + 2t Re Tr(a(ω f) Γ) + t² ‖√ω f‖²` for every real
`t`. Minimality forces `Re Tr(a(ω f) Γ) = 0`.

The smeared transverse electric field along `g` is
`E_⊥(g) = -i (a†(ω g) - a(ω g))`, with expectation `-2 Im ⟨u, a(ω g) u⟩`. When
`⟨κ_b(x), g⟩` is real for every coordinate `b` and almost every `x`, the
direction `f = i g` is real, which gives `Tr(E_⊥(g) Γ) = 0`.
-/

noncomputable section

namespace GptLean.PhysicalWeyl

open MeasureTheory Filter PhysicalFock PhysicalPFReference PhysicalPFSoftTag
  PhysicalNormalTrace Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000


section Vector

theorem re_inner_real_smul_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b : E) (t : ℝ) : (⟪starRingEnd ℂ (t : ℂ) • a, b⟫_ℂ).re = t * (⟪a, b⟫_ℂ).re := by
  rw [Complex.conj_ofReal, inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]

theorem im_inner_I {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a b : E) :
    (⟪b, a⟫_ℂ).im = (⟪starRingEnd ℂ Complex.I • a, b⟫_ℂ).re := by
  rw [inner_smul_left, ← inner_conj_symm a b]
  simp [Complex.mul_re]
  rw [← inner_conj_symm a b, Complex.conj_im, neg_neg]

variable {I : Type} [Fintype I] [DecidableEq I] (V : Position I → ℝ)

theorem annihilationRef_smul (c : ℂ) (k : WeightedPhotonKernel) (u : Reference I V) :
    annihilationRef V (c • k) u = starRingEnd ℂ c • annihilationRef V k u := by
  apply Lp.ext
  filter_upwards [(kernelAnnihilation (c • k)).coeFn_compLpL (radiationSource I V u),
    (kernelAnnihilation k).coeFn_compLpL (radiationSource I V u),
    Lp.coeFn_smul (starRingEnd ℂ c) (annihilationRef V k u)] with x h₁ h₂ h₃
  have h₁' : annihilationRef V (c • k) u x =
      kernelAnnihilation (c • k) (radiationSource I V u x) := h₁
  have h₂' : annihilationRef V k u x = kernelAnnihilation k (radiationSource I V u x) := h₂
  have hk : kernelAnnihilation (c • k) (radiationSource I V u x) =
      starRingEnd ℂ c • kernelAnnihilation k (radiationSource I V u x) :=
    congrArg (fun L => L (radiationSource I V u x)) (kernelAnnihilation_smul c k)
  exact h₁'.trans (hk.trans ((congrArg (fun y : PhotonFock => starRingEnd ℂ c • y)
    h₂'.symm).trans h₃.symm))

theorem amplitude_re_le (k : WeightedPhotonKernel) (u : Reference I V) :
    ‖⟪annihilationRef V k u, inclusion I V u⟫_ℂ‖ ≤
      ‖k.val.2‖ * (‖radiation I V u‖ ^ 2 + ‖inclusion I V u‖ ^ 2) := by
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (annihilationRef V k u) (inclusion I V u)
  have h2 := annihilationRef_norm_le V k u
  have hk := norm_nonneg k.val.2
  have hr := norm_nonneg (radiation I V u)
  have hu := norm_nonneg (inclusion I V u)
  calc ‖⟪annihilationRef V k u, inclusion I V u⟫_ℂ‖
      ≤ ‖annihilationRef V k u‖ * ‖inclusion I V u‖ := h1
    _ ≤ ‖k.val.2‖ * ‖radiation I V u‖ * ‖inclusion I V u‖ :=
        mul_le_mul_of_nonneg_right h2 hu
    _ ≤ _ := by nlinarith [sq_nonneg (‖radiation I V u‖ - ‖inclusion I V u‖)]

end Vector

section Optimizer

variable {N : ℕ} (i : Fin N) (V : Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ b, AEStronglyMeasurable (κ b) volume)
  (M : ℝ) (hbound : ∀ b, ∀ᵐ x ∂volume, ‖κ b x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (e : ℝ) (W : ConcreteWeylLaw photonMeasure)

theorem amplitude_summable {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B x)
    (he : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation x < ⊤)
    (k : WeightedPhotonKernel) :
    Summable (fun n => ⟪annihilationRef V k (s.vector n),
      inclusion (Fin N × Fin 3) V (s.vector n)⟫_ℂ) := by
  refine Summable.of_norm_bounded
    (((s.energy_hasSum C κ hκ M hbound S e he).summable.add s.mass_hasSum.summable).mul_left
      ‖k.val.2‖) fun n => (amplitude_re_le V k (s.vector n)).trans ?_
  exact mul_le_mul_of_nonneg_left (add_le_add
    (radiation_le_energy (Fin N × Fin 3) V C κ hκ M hbound e (s.vector n)) le_rfl) (norm_nonneg _)

set_option backward.isDefEq.respectTransparency.types true in
/-- A spectral source of a density matrix has total mass one. -/
theorem source_mass_one (m : PhysicalPFStates.MixedState V C κ hκ M hbound B S e)
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B m.val.val) :
    HasSum (fun n => ‖inclusion (Fin N × Fin 3) V (s.vector n)‖ ^ 2) 1 := by
  have h : HasSum (fun n => ‖inclusion (Fin N × Fin 3) V (s.vector n)‖ ^ 2)
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.trace m.val.val) := s.mass_hasSum
  have htrace : (B.realization (WaveSpace (Fin N × Fin 3))).rank.trace m.val.val = 1 :=
    m.val.property.2.1
  exact (congrArg (HasSum (fun n => ‖inclusion (Fin N × Fin 3) V (s.vector n)‖ ^ 2)) htrace).mp h

/-- The scaled direction. -/
theorem scaled_kernel {f : Lp ℂ 2 photonMeasure} {K : WeightedPhotonKernel}
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p) (c : ℂ) :
    ∀ᵐ p ∂photonMeasure, (c • K).val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * (c • f) p := by
  filter_upwards [hK, Lp.coeFn_smul c K.val.2, Lp.coeFn_smul c f] with p h₁ h₂ h₃
  change (c • K.val.2) p = _
  rw [h₂, h₃, Pi.smul_apply, Pi.smul_apply, h₁, smul_eq_mul, smul_eq_mul]
  ring

theorem classicalField_smul (f : Lp ℂ 2 photonMeasure) (t : ℝ) (b : Fin N × Fin 3)
    (x : Position (Fin N × Fin 3)) :
    classicalField κ ((t : ℂ) • f) b x = t * classicalField κ f b x := by
  unfold classicalField
  rw [inner_smul_right, Complex.re_ofReal_mul]
  ring

theorem classicalField_I (g : Lp ℂ 2 photonMeasure) (b : Fin N × Fin 3)
    (x : Position (Fin N × Fin 3)) :
    classicalField κ (Complex.I • g) b x = -2 * (⟪(κ b x).val.1, g⟫_ℂ).im := by
  unfold classicalField
  rw [inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

theorem amplitude_scaled (t : ℝ) (k : WeightedPhotonKernel) (u : Reference (Fin N × Fin 3) V) :
    (⟪annihilationRef V ((t : ℂ) • k) u, inclusion (Fin N × Fin 3) V u⟫_ℂ).re =
      t * (⟪annihilationRef V k u, inclusion (Fin N × Fin 3) V u⟫_ℂ).re :=
  (congrArg (fun z => (⟪z, inclusion (Fin N × Fin 3) V u⟫_ℂ).re)
    (annihilationRef_smul V (t : ℂ) k u)).trans (re_inner_real_smul_left _ _ t)

theorem kernel_scaled_norm_sq (t : ℝ) (k : WeightedPhotonKernel) :
    ‖((t : ℂ) • k).val.2‖ ^ 2 = t ^ 2 * ‖k.val.2‖ ^ 2 := by
  change ‖(t : ℂ) • k.val.2‖ ^ 2 = _
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem amplitude_I (k : WeightedPhotonKernel) (u : Reference (Fin N × Fin 3) V) :
    (⟪inclusion (Fin N × Fin 3) V u, annihilationRef V k u⟫_ℂ).im =
      (⟪annihilationRef V (Complex.I • k) u, inclusion (Fin N × Fin 3) V u⟫_ℂ).re :=
  (im_inner_I _ _).trans (congrArg (fun z => (⟪z, inclusion (Fin N × Fin 3) V u⟫_ℂ).re)
    (annihilationRef_smul V Complex.I k u)).symm

theorem energy_curve_term (t : ℝ) {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (hreal : ∀ b, ∀ᵐ x ∂volume, classicalField κ f b x = 0) (u : Reference (Fin N × Fin 3) V) :
    energy (Fin N × Fin 3) V C κ hκ M hbound e
        (weylRef V W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) u) =
      energy (Fin N × Fin 3) V C κ hκ M hbound e u +
        2 * (t * (⟪annihilationRef V K u, inclusion (Fin N × Fin 3) V u⟫_ℂ).re) +
        t ^ 2 * ‖K.val.2‖ ^ 2 * ‖inclusion (Fin N × Fin 3) V u‖ ^ 2 := by
  have hrt : ∀ b, ∀ᵐ x ∂volume, classicalField κ ((t : ℂ) • f) b x = 0 := fun b =>
    (hreal b).mono fun x hx => by rw [classicalField_smul, hx, mul_zero]
  exact (energy_weylRef_of_real V W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) C κ hκ M hbound e
    hrt u).trans (congrArg₂ (fun a b : ℝ => energy (Fin N × Fin 3) V C κ hκ M hbound e u + 2 * a +
      b * ‖inclusion (Fin N × Fin 3) V u‖ ^ 2) (amplitude_scaled V t K u) (kernel_scaled_norm_sq t K))

include W in
/-- **Optimizers have no real linear energy response.** For a real direction `f`,
`∑ₙ Re ⟨a(ω f) uₙ, uₙ⟩ = 0` for every spectral source of an optimizer. -/
theorem optimizer_real_amplitude (m : PhysicalPFStates.MixedState V C κ hκ M hbound B S e)
    (hopt : ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).energy m : EReal) =
      DFT.search (PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e)
        ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density m))
    {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (hreal : ∀ b, ∀ᵐ x ∂volume, classicalField κ f b x = 0)
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B m.val.val) :
    ∑' n, (⟪annihilationRef V K (s.vector n), inclusion (Fin N × Fin 3) V (s.vector n)⟫_ℂ).re =
      0 := by
  have he := m.val.property.2.2
  have hE : HasSum (fun n => energy (Fin N × Fin 3) V C κ hκ M hbound e (s.vector n))
      ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).energy m) :=
    s.energy_hasSum C κ hκ M hbound S e he
  have hM := source_mass_one V C κ hκ M hbound B S e m s
  have hA := Complex.hasSum_re (amplitude_summable V C κ hκ M hbound B S e s he K).hasSum
  have hcurve : ∀ t : ℝ, 0 ≤ 2 * t * (∑' n, ⟪annihilationRef V K (s.vector n),
      inclusion (Fin N × Fin 3) V (s.vector n)⟫_ℂ).re + t ^ 2 * ‖K.val.2‖ ^ 2 := by
    intro t
    have hrt : ∀ b, ∀ᵐ x ∂volume, classicalField κ ((t : ℂ) • f) b x = 0 := fun b =>
      (hreal b).mono fun x hx => by rw [classicalField_smul, hx, mul_zero]
    have h1 := weylState_energy_hasSum i V C κ hκ M hbound B S e W ((t : ℂ) • K)
      (scaled_kernel hK (t : ℂ)) m s
    simp only [energy_curve_term V C κ hκ M hbound e W t K hK hreal] at h1
    have h2 := (hE.add ((hA.mul_left t).mul_left 2)).add
      (hM.mul_left (t ^ 2 * ‖K.val.2‖ ^ 2))
    have heq := h1.unique h2
    have hd := weylState_density_of_real i V C κ hκ M hbound B S e W ((t : ℂ) • K)
      (scaled_kernel hK (t : ℂ)) hrt m
    have hle : ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).energy m : EReal) ≤
        ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).energy
          (weylState V C κ hκ M hbound B S e W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) m) :
            EReal) :=
      hopt.trans_le (DFT.search_le _ hd)
    have hle' := EReal.coe_le_coe_iff.mp hle
    linarith
  exact hA.tsum_eq.trans (linear_coefficient_zero (sq_nonneg _) hcurve)

/-- The expectation `Tr(E_⊥(g) Γ) = -2 Im Tr(a(ω g) Γ)` of the smeared transverse
electric field, for the weighted kernel `K = (ω g, √ω g)`. -/
def electricExpectation {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B x) (K : WeightedPhotonKernel) : ℝ :=
  -2 * (sourceAmplitude V B s K).im

include W in
/-- **`optimizer-mean-electric-zero`.** If `⟨κ_b(x), g⟩` is real for every
coordinate `b` and almost every configuration `x`, the mean transverse electric
field of every optimizer along `g` vanishes, in every spectral source. -/
theorem optimizer_electric_zero (m : PhysicalPFStates.MixedState V C κ hκ M hbound B S e)
    (hopt : ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).energy m : EReal) =
      DFT.search (PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e)
        ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density m))
    {g : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (hgreal : ∀ b, ∀ᵐ x ∂volume, (⟪(κ b x).val.1, g⟫_ℂ).im = 0)
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B m.val.val) :
    electricExpectation V B s K = 0 := by
  have he := m.val.property.2.2
  have hreal : ∀ b, ∀ᵐ x ∂volume, classicalField κ (Complex.I • g) b x = 0 := fun b =>
    (hgreal b).mono fun x hx => by rw [classicalField_I, hx, mul_zero]
  have h0 := optimizer_real_amplitude i V C κ hκ M hbound B S e W m hopt (Complex.I • K)
    (scaled_kernel hK Complex.I) hreal s
  have hs : Summable (fun n => ⟪inclusion (Fin N × Fin 3) V (s.vector n),
      annihilationRef V K (s.vector n)⟫_ℂ) :=
    ((amplitude_summable V C κ hκ M hbound B S e s he K).map (starRingEnd ℂ)
      Complex.continuous_conj).congr fun n => inner_conj_symm _ _
  have hIm := Complex.hasSum_im hs.hasSum
  unfold electricExpectation sourceAmplitude
  rw [hIm.tsum_eq.symm.trans (tsum_congr fun n => amplitude_I V K (s.vector n)), h0, mul_zero]

end Optimizer

end GptLean.PhysicalWeyl
