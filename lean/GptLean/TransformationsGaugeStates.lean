import GptLean.TransformationsGaugeReference
import GptLean.TransformationsGaugePair
import GptLean.TransformationsPureStates
import GptLean.TransformationsPotentials

/-!
Gauge covariance of the Levy--Lieb and Lieb functionals on the actual
Pauli--Fierz model, `prop-gauge-covariance`, for a gauge function with
bounded gradient.

For `G(X) = ∑ⱼ g(xⱼ)`, the phase `U_g = exp (i G)` maps pure states to pure
states, with inverse `U_{-g}`. The constructed density-current pair obeys
`ρ_{U_g Ψ} = ρ_Ψ` and `j_{U_g Ψ} = j_Ψ + ρ_Ψ ∇g`. On fermionic states the
internal energy obeys `energy-gauge`, with the cross term identified with
`∫ ∇g · j` and the quadratic term with `½ ∫ ρ |∇g|²` through the summed
particle tests. Hence

`F(ρ, j + ρ ∇g) = F(ρ, j) + ∫ ∇g · j + ½ ∫ ρ |∇g|²`

for `F = F_LL` and for the Lieb functional `F = F_L`, for every pair in the
article space, including empty constraint sets.
-/

noncomputable section

namespace GptLean.TransformationsGauge

open MeasureTheory PhysicalFock PhysicalPFReference SymmetricLift PhysicalPairSpace
  PhysicalNormalTrace PhysicalClosedForms TransformationsPhase
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem re_inner_real_smul (a b : E) (s : ℝ) : (⟪a, s • b⟫_ℂ).re = s * (⟪b, a⟫_ℂ).re := by
  rw [← Complex.coe_smul, inner_smul_right, Complex.re_ofReal_mul]
  congr 1
  rw [← inner_conj_symm, Complex.conj_re]

theorem norm_real_smul_sq (b : E) (s : ℝ) : ‖s • b‖ ^ 2 = s ^ 2 * ‖b‖ ^ 2 := by
  rw [← Complex.coe_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The phase drops out of the current component and adds `s ‖a‖²`. -/
theorem phase_current (f : ℂ) (hf : ‖f‖ = 1) (a b : E) (s : ℝ) :
    (⟪f • a, f • (b + s • a)⟫_ℂ).re = (⟪a, b⟫_ℂ).re + s * ‖a‖ ^ 2 := by
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, hf, one_pow, Complex.ofReal_one, one_mul, inner_add_right,
    Complex.add_re, ← Complex.coe_smul, inner_smul_right, Complex.re_ofReal_mul,
    inner_self_eq_norm_sq_to_K]
  norm_cast

theorem phase_norm (f : ℂ) (hf : ‖f‖ = 1) (a : E) : ‖f • a‖ = ‖a‖ := by
  rw [norm_smul, hf, one_mul]

theorem l2_norm_sq_complex {X : Type*} [MeasurableSpace X] {μ : Measure X} (v : Lp E 2 μ) :
    ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) v, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) v v)]
  congr 1
  funext x
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (v x)).symm

theorem current_algebra {P : Type*} (t g : P → ℝ) {y y' : P} (h : y = y') (A Bn : ℝ) :
    t y * (A + g y' * Bn) = t y * A + (t y * g y) * Bn := by
  subst h
  ring

theorem sum_sq_mul {N : ℕ} (f : Fin N × Fin 3 → ℝ) (h : Fin N → Fin 3 → ℝ)
    (hf : ∀ j a, f (j, a) = h j a) (t : ℝ) :
    (∑ q, f q ^ 2 * t) = (∑ j, ∑ a, h j a ^ 2) * t := by
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by rw [hf]

end Algebra

section Integrals

variable {I : Type} [Fintype I] [DecidableEq I] (G : GaugeFunction I)

/-- The cross term as an integral of the pointwise current component. -/
theorem re_inner_gradientMultiplier (q : I) (d w : WaveSpace I) :
    (⟪d, G.gradientMultiplier q w⟫_ℂ).re =
      ∫ z, G.gradient q z * PhysicalPairIntegrability.currentComponent (w z) (d z) := by
  have h₁ : ⟪d, G.gradientMultiplier q w⟫_ℂ = ∫ a, ⟪d a, G.gradientMultiplier q w a⟫_ℂ :=
    L2.inner_def d (G.gradientMultiplier q w)
  have h₂ := integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) d (G.gradientMultiplier q w))
  simp only [RCLike.re_to_complex] at h₂
  refine (congrArg Complex.re h₁).trans (h₂.symm.trans ?_)
  apply integral_congr_ae
  filter_upwards [G.gradientMultiplier_ae q w] with z hz
  exact (congrArg (fun y => (⟪d z, y⟫_ℂ).re) hz).trans (re_inner_real_smul _ _ _)

/-- The quadratic term as an integral of the pointwise density. -/
theorem norm_sq_gradientMultiplier (q : I) (w : WaveSpace I) :
    ‖G.gradientMultiplier q w‖ ^ 2 = ∫ z, G.gradient q z ^ 2 * ‖w z‖ ^ 2 := by
  refine (l2_norm_sq_complex _).trans ?_
  apply integral_congr_ae
  filter_upwards [G.gradientMultiplier_ae q w] with z hz
  exact (congrArg (fun y => ‖y‖ ^ 2) hz).trans (norm_real_smul_sq _ _)

theorem currentComponent_integrable (q : I) (d w : WaveSpace I) :
    Integrable (fun z => G.gradient q z *
      PhysicalPairIntegrability.currentComponent (w z) (d z)) volume := by
  have hi : Integrable (fun z => PhysicalPairIntegrability.currentComponent (w z) (d z)) volume :=
    (L2.integrable_inner (𝕜 := ℂ) w d).re.congr (ae_of_all _ fun z => RCLike.re_to_complex)
  refine hi.bdd_mul (G.gradient_measurable q).aestronglyMeasurable
    (c := G.derivativeBound) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  exact G.gradient_bounded q z

theorem density_integrable (q : I) (w : WaveSpace I) :
    Integrable (fun z => G.gradient q z ^ 2 * ‖w z‖ ^ 2) volume := by
  have hi : Integrable (fun z => ‖w z‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable w)).mp (Lp.memLp w)
  refine hi.bdd_mul ((G.gradient_measurable q).pow_const 2).aestronglyMeasurable
    (c := G.derivativeBound ^ 2) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (G.gradient_bounded q z) 2

end Integrals

namespace SpatialGauge

variable (g : SpatialGauge) {N : ℕ}
  (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M) (e : ℝ) (i : Fin N)

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM

/-- The configuration phase, which is the gauge transformation of wave functions. -/
abbrev configurationPhase (g : SpatialGauge) (N : ℕ) :
    WaveSpace (Fin N × Fin 3) ≃ₗᵢ[ℂ] WaveSpace (Fin N × Fin 3) :=
  (g.configuration N).wavePhase

theorem configurationPhase_ae (w : WaveSpace (Fin N × Fin 3)) :
    g.configurationPhase N w =ᵐ[volume] fun x => factor (g.configuration N).fn x • w x :=
  (g.configuration N).phaseL2_ae (H := PhotonFock) w

/-- The gauge-transformed constructed pair is the shifted pair. -/
theorem pair_gauge (u : Reference (Fin N × Fin 3) V) :
    PhysicalPFParticle.pair C K hK M hM V i e ((g.configuration N).gaugeReference V u) =
      g.shiftPair (PhysicalPFParticle.pair C K hK M hM V i e u) := by
  let T := (g.configuration N).gaugeReference V u
  have hincl : ⇑(inclusion (Fin N × Fin 3) V T) =ᵐ[volume]
      fun z => factor (g.configuration N).fn z • inclusion (Fin N × Fin 3) V u z :=
    (Filter.EventuallyEq.of_eq (congrArg (fun w : WaveSpace (Fin N × Fin 3) => ⇑w)
      ((g.configuration N).inclusion_gaugeReference V u))).trans
      (g.configurationPhase_ae (inclusion (Fin N × Fin 3) V u))
  apply pair_eq_of_bounded_spatial_tests
  · intro t
    refine Eq.trans ?_ (g.tested_density_shiftPair _ t.weight).symm
    refine (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V T))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) T) t.weight t.measurable
      (ae_of_all _ t.bounded)).trans (Eq.trans ?_ (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) t.weight t.measurable
      (ae_of_all _ t.bounded)).symm)
    refine congrArg (fun r : ℝ => (N : ℝ) * r) (integral_congr_ae ?_)
    filter_upwards [hincl] with z hz
    exact (congrArg (fun y : PhotonFock => t.weight ((PhysicalSourceCoordinates.split i) z).1 *
      ‖y‖ ^ 2) hz).trans (congrArg (fun r : ℝ => t.weight ((PhysicalSourceCoordinates.split i) z).1 *
        r ^ 2) (phase_norm _ (norm_factor _ z) _))
  · intro b t
    have hbt : ∀ x, ‖t.weight x‖ ≤ 1 := t.bounded
    have hcov := (g.configuration N).covariant_gaugeReference V C κP hκP M hbP e (i, b) u
    have hD : ⇑(covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) T) =ᵐ[volume]
        fun z => factor (g.configuration N).fn z •
          (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u z +
            g.gradient b (particle z i) • inclusion (Fin N × Fin 3) V u z) := by
      filter_upwards [Filter.EventuallyEq.of_eq (congrArg (fun w : WaveSpace (Fin N × Fin 3) => ⇑w)
          hcov),
        g.configurationPhase_ae (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u +
          (g.configuration N).gradientMultiplier (i, b) (inclusion (Fin N × Fin 3) V u)),
        Lp.coeFn_add (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u)
          ((g.configuration N).gradientMultiplier (i, b) (inclusion (Fin N × Fin 3) V u)),
        (g.configuration N).gradientMultiplier_ae (i, b) (inclusion (Fin N × Fin 3) V u)]
        with z h₁ h₂ h₃ h₄
      refine h₁.trans (h₂.trans (congrArg (fun y => factor (g.configuration N).fn z • y)
        (h₃.trans (congrArg (fun y => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u z + y)
          (h₄.trans (congrArg (fun r : ℝ => r • inclusion (Fin N × Fin 3) V u z)
            (g.configuration_gradient (i, b) z)))))))
    have htb : AEStronglyMeasurable (fun x => t.weight x * g.gradient b x) volume :=
      t.measurable.mul (g.gradient_measurable b).aestronglyMeasurable
    have hbound : ∀ᵐ x ∂volume, ‖t.weight x * g.gradient b x‖ ≤ g.derivativeBound :=
      ae_of_all _ fun x => by
        rw [norm_mul]
        calc ‖t.weight x‖ * ‖g.gradient b x‖ ≤ 1 * g.derivativeBound :=
              mul_le_mul (hbt x) (by rw [Real.norm_eq_abs]; exact g.abs_gradient_le b x)
                (norm_nonneg _) zero_le_one
          _ = g.derivativeBound := one_mul _
    refine Eq.trans ?_ (g.tested_current_shiftPair _ b t.weight t.measurable hbt).symm
    refine (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V T))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) T) b t.weight t.measurable
      (ae_of_all _ t.bounded)).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· + ·) (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) b t.weight t.measurable
      (ae_of_all _ t.bounded)).symm (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) _ htb hbound).symm)
    have hmeas : AEStronglyMeasurable
        (fun z => t.weight ((PhysicalSourceCoordinates.split i) z).1) volume :=
      t.measurable.comp_fst.comp_measurePreserving
        (PhysicalSourceCoordinates.split_measurePreserving i)
    have hi₁ : Integrable (fun z => t.weight ((PhysicalSourceCoordinates.split i) z).1 *
        (⟪inclusion (Fin N × Fin 3) V u z,
          covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u z⟫_ℂ).re) volume :=
      ((L2.integrable_inner (𝕜 := ℂ) _ _).re.congr (ae_of_all _ fun z =>
        RCLike.re_to_complex)).bdd_mul hmeas (c := 1) (ae_of_all _ fun z => hbt _)
    have hi₂ : Integrable (fun z => (t.weight ((PhysicalSourceCoordinates.split i) z).1 *
        g.gradient b ((PhysicalSourceCoordinates.split i) z).1) *
        ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2) volume :=
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp
        (Lp.memLp _)).bdd_mul (htb.comp_fst.comp_measurePreserving
          (PhysicalSourceCoordinates.split_measurePreserving i))
        (c := g.derivativeBound) (ae_of_all _ fun z => by
          rw [norm_mul]
          calc _ ≤ 1 * g.derivativeBound :=
                mul_le_mul (hbt _) (by rw [Real.norm_eq_abs]; exact g.abs_gradient_le b _)
                  (norm_nonneg _) zero_le_one
            _ = g.derivativeBound := one_mul _)
    refine Eq.trans ?_ (mul_add _ _ _)
    refine congrArg (fun r : ℝ => (N : ℝ) * r) (Eq.trans ?_ (integral_add hi₁ hi₂))
    apply integral_congr_ae
    filter_upwards [hincl, hD] with z h₁ h₂
    change t.weight _ * (⟪inclusion (Fin N × Fin 3) V T z,
        covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) T z⟫_ℂ).re = _
    refine (congrArg₂ (fun a c => t.weight ((PhysicalSourceCoordinates.split i) z).1 *
      (⟪a, c⟫_ℂ).re) h₁ h₂).trans ?_
    refine (congrArg (fun r : ℝ => t.weight ((PhysicalSourceCoordinates.split i) z).1 * r)
      (phase_current _ (norm_factor _ z) _ _ _)).trans ?_
    exact current_algebra t.weight (g.gradient b) (PhysicalSourcePair.split_fst_eq_particle i z) _ _

variable {g V C K hK M hM}

/-- For fermionic vectors the cross and quadratic terms are the paired
energy shift `∫ ∇g · j + ½ ∫ ρ |∇g|²`. -/
theorem energy_gauge (u : Reference (Fin N × Fin 3) V)
    (hu : inclusion (Fin N × Fin 3) V u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    energy (Fin N × Fin 3) V C κP hκP M hbP e ((g.configuration N).gaugeReference V u) =
      energy (Fin N × Fin 3) V C κP hκP M hbP e u +
        g.energyShift (PhysicalPFParticle.pair C K hK M hM V i e u) := by
  refine ((g.configuration N).energy_gaugeReference V C κP hκP M hbP e u).trans ?_
  rw [add_assoc]
  refine congrArg (fun r : ℝ => energy (Fin N × Fin 3) V C κP hκP M hbP e u + r) ?_
  unfold energyShift
  refine congrArg₂ (· + ·) ?_ ?_
  · -- the cross term is the tested current
    have h (q : Fin N × Fin 3) := re_inner_gradientMultiplier (g.configuration N) q
      (covariant (Fin N × Fin 3) V C κP hκP M hbP e q u) (inclusion (Fin N × Fin 3) V u)
    refine (Finset.sum_congr rfl fun q _ => h q).trans ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Eq.trans ?_ (PhysicalPFParticle.pair_tested_current C K hK M hM V i e u hu b
      (g.gradient b) (g.gradient_measurable b) (b := g.derivativeBound)
      (fun x => by rw [Real.norm_eq_abs]; exact g.abs_gradient_le b x)).symm
    refine (integral_finsetSum _ (fun j _ =>
      currentComponent_integrable (g.configuration N) (j, b) _ _)).symm.trans ?_
    apply integral_congr_ae
    refine ae_of_all _ fun z => Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (fun r : ℝ => r * _) (g.configuration_gradient (j, b) z)
  · -- the quadratic term is the tested density
    have hf : Measurable (fun y => ∑ a, g.gradient a y ^ 2) :=
      Finset.measurable_sum _ fun a _ => (g.gradient_measurable a).pow_const 2
    refine congrArg (fun r : ℝ => (1 / 2 : ℝ) * r) ?_
    refine (Finset.sum_congr rfl fun q _ =>
      norm_sq_gradientMultiplier (g.configuration N) q (inclusion (Fin N × Fin 3) V u)).trans ?_
    refine (integral_finsetSum _ (fun q _ => density_integrable _ q _)).symm.trans ?_
    refine Eq.trans ?_ (PhysicalPFParticle.pair_tested_density C K hK M hM V i e u hu
      (fun y => ∑ a, g.gradient a y ^ 2) hf (b := 3 * g.derivativeBound ^ 2)
      (fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun a _ => sq_nonneg _)]
        calc (∑ a, g.gradient a y ^ 2) ≤ ∑ _a : Fin 3, g.derivativeBound ^ 2 :=
              Finset.sum_le_sum fun a _ => by
                rw [← sq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _) (g.abs_gradient_le a y) 2
          _ = 3 * g.derivativeBound ^ 2 := by simp)).symm
    apply integral_congr_ae
    refine ae_of_all _ fun z => ?_
    exact sum_sq_mul (fun q => (g.configuration N).gradient q z)
      (fun j a => g.gradient a (particle z j)) (fun j a => g.configuration_gradient (j, a) z) _

theorem configurationPhase_neg (w : WaveSpace (Fin N × Fin 3)) :
    g.neg.configurationPhase N (g.configurationPhase N w) = w := by
  apply Lp.ext
  filter_upwards [g.neg.configurationPhase_ae (g.configurationPhase N w),
    g.configurationPhase_ae w] with x h₁ h₂
  refine h₁.trans ((congrArg (fun y => factor (g.neg.configuration N).fn x • y) h₂).trans ?_)
  rw [smul_smul]
  have hx : factor (g.neg.configuration N).fn x * factor (g.configuration N).fn x = 1 := by
    rw [← factor_add]
    have h0 : ((g.neg.configuration N).fn + (g.configuration N).fn) x = 0 := by
      change (∑ j, -g.fn (particle x j)) + ∑ j, g.fn (particle x j) = 0
      rw [Finset.sum_neg_distrib, neg_add_cancel]
    simp only [factor, h0, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [hx, one_smul]

theorem configurationPhase_neg_left (w : WaveSpace (Fin N × Fin 3)) :
    g.configurationPhase N (g.neg.configurationPhase N w) = w := by
  apply Lp.ext
  filter_upwards [g.configurationPhase_ae (g.neg.configurationPhase N w),
    g.neg.configurationPhase_ae w] with x h₁ h₂
  refine h₁.trans ((congrArg (fun y => factor (g.configuration N).fn x • y) h₂).trans ?_)
  rw [smul_smul]
  have hx : factor (g.configuration N).fn x * factor (g.neg.configuration N).fn x = 1 := by
    rw [← factor_add]
    have h0 : ((g.configuration N).fn + (g.neg.configuration N).fn) x = 0 := by
      change (∑ j, g.fn (particle x j)) + ∑ j, -g.fn (particle x j) = 0
      rw [Finset.sum_neg_distrib, add_neg_cancel]
    simp only [factor, h0, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [hx, one_smul]

variable (g V C K hK M hM)

/-- **Gauge covariance of `F_LL`** (`F-gauge` for the pure functional), for a
gauge function with bounded gradient, on the constructed Pauli--Fierz model.
It holds for every pair in the article space, including empty fibres. -/
theorem search_gauge (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)
    (d : Pair) :
    DFT.search (TransformationsPureStates.pureModel V C K hK M hM B S e i) (g.shiftPair d) =
      DFT.search (TransformationsPureStates.pureModel V C K hK M hM B S e i) d +
        ((g.energyShift d : ℝ) : EReal) :=
  TransformationsPureStates.search_covariance_of_reference V C K hK M hM B S e i
    (g.configurationPhase N) (g.neg.configurationPhase N) g.shiftEquiv g.energyShift
    (fun v => (g.configurationPhase N).norm_map v)
    (fun v => (g.neg.configurationPhase N).norm_map v)
    (fun v hv => g.phaseL2_mem_fermionic hv) (fun v hv => g.neg.phaseL2_mem_fermionic hv)
    configurationPhase_neg configurationPhase_neg_left
    (fun u => ⟨(g.neg.configuration N).gaugeReference V u,
      (g.neg.configuration N).inclusion_gaugeReference V u⟩)
    (fun u hu => ⟨(g.configuration N).gaugeReference V u,
      (g.configuration N).inclusion_gaugeReference V u, energy_gauge e i u hu,
      g.pair_gauge V C K hK M hM e i u⟩) d

/-- **Gauge covariance of the Lieb functional** `F_L`, obtained from the
covariance of `F_LL` and the potential shift `(v, A) ↦ (v + A·∇g + ½|∇g|², A + ∇g)`. -/
theorem lieb_gauge (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)
    (d : Pair) :
    DFT.lieb (TransformationsPureStates.pureModel V C K hK M hM B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) (g.shiftPair d) =
      DFT.lieb (TransformationsPureStates.pureModel V C K hK M hM B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) d +
        ((g.energyShift d : ℝ) : EReal) :=
  TransformationsPotentials.lieb_gauge g _ (g.search_gauge V C K hK M hM e i B S) d

end SpatialGauge

end GptLean.TransformationsGauge
