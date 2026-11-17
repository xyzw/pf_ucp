import GptLean.PhysicalMeanFieldsWeighted
import GptLean.PhysicalPureFunctional
import GptLean.TransformationsGaugeStates

/-!
`prop-optimizer-mean-fields` (iii) for currents of gradient form `j = ρ ∇S`,
with `∇S` bounded.

Let `Γ` minimize the energy at `d = (ρ, ρ ∇S)` and put `g = -S`, so that the
gauge shift sends `d` to `(ρ, 0)`. The gauge covariance of `F_LL`, transported
to the mixed functional by `F_LL = F̃_L`, gives

`F̃_L(ρ, 0) = F̃_L(d) + E_g(d) = Tr(H Γ) + E_g(d)`,

with `E_g(p) = ∫ ∇g · j + ½ ∫ ρ |∇g|²`. For any density matrix `Γ'` with
density `ρ`, the shifted pair of `Γ'` has density `ρ`, so by the zero-current
density search

`F̃_L(ρ, 0) ≤ F̃_L(p_{Γ'}) + E_g(p_{Γ'}) ≤ Tr(H Γ') + E_g(p_{Γ'})`.

For `Γ' = Γ_t`, the displacement of `Γ` by `t f`, the density is unchanged and the
current becomes `j - e t ρ c_f`, where `c_f^a(y) = 2 Re ⟨G^a_y, f⟩`. Hence
`E_g(p_{Γ_t}) = E_g(d) + e t J` with `J = ∫ c_f · j`, which is exactly the
current term in `Tr(H Γ_t) = Tr(H Γ) + 2t Re Tr(a(ω f) Γ) - e t J + O(t²)`. The
two `J` terms cancel, so `Re Tr(a(ω f) Γ) = 0`. The rest of the argument is the
zero-current one: the direction `i f` gives the imaginary part, and the
frequency windows extend the result to every coherent amplitude and to the mean
vector potential.
-/

noncomputable section

namespace GptLean.PhysicalWeyl

open MeasureTheory Filter PhysicalFock PhysicalPFReference PhysicalPFSoftTag
  PhysicalNormalTrace PhysicalPairSpace Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem re_inner_weyl_shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (L : E ≃ₗᵢ[ℂ] E) (a d : E) (r : ℝ) :
    (⟪L a, L (d - (r : ℂ) • a)⟫_ℂ).re = (⟪a, d⟫_ℂ).re - r * ‖a‖ ^ 2 := by
  rw [LinearIsometryEquiv.inner_map_map, inner_sub_right, inner_smul_right, Complex.sub_re,
    Complex.re_ofReal_mul, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem shift_algebra {P : Type*} (w c : P → ℝ) {y y' : P} (h : y = y') (R n e : ℝ) :
    w y * (R - e * c y' * n) = w y * R - e * ((w y * c y) * n) := by
  subst h
  ring

theorem mul_sub_algebra (n x y e : ℝ) : n * (x - e * y) = n * x - e * (n * y) := by ring

theorem energyShift_algebra {S₁ S₂ D₁ D₂ T c : ℝ} (hS : S₁ = S₂ + c * T) (hD : D₁ = D₂) :
    S₁ + (1 / 2 : ℝ) * D₁ = (S₂ + (1 / 2 : ℝ) * D₂) + c * T := by
  rw [hS, hD]
  ring

/-- The last step of the gradient-current curve argument, over the reals. -/
theorem curve_gauge {E E' A Kn Q J J' X X' t e : ℝ}
    (heq : E' = E + 2 * (t * A) + t ^ 2 * Kn * 1 + (-(e * t) * J + e ^ 2 * t ^ 2 / 2 * Q))
    (hJ : J = J') (hle : E + X ≤ E' + X') (hX : X' = X + e * t * J') :
    0 ≤ 2 * t * A + t ^ 2 * (Kn + e ^ 2 / 2 * Q) := by
  have h : 2 * t * A + t ^ 2 * (Kn + e ^ 2 / 2 * Q) = (E' + X') - (E + X) := by
    rw [heq, hX, hJ]
    ring
  rw [h]
  exact sub_nonneg.mpr hle

theorem current_algebra' {L A A' D T e t : ℝ} (h : L = A - e * D) (hA : A = A')
    (hD : D = -(t * T)) : L = A' + e * t * T := by
  rw [h, hA, hD]
  ring

section Tests

/-- A bounded weight, rescaled into a spatial test. -/
def scaledTest (w : PhysicalPairSpace.Position → ℝ) (hw : AEStronglyMeasurable w volume)
    {L : ℝ} (hL : ∀ y, ‖w y‖ ≤ L) : SpatialTest where
  weight y := w y / (L + 1)
  measurable := (hw.aemeasurable.div_const _).aestronglyMeasurable
  bounded y := by
    have hpos : 0 < L + 1 := by linarith [(norm_nonneg _).trans (hL y)]
    rw [norm_div, Real.norm_of_nonneg hpos.le, div_le_one hpos]
    linarith [hL y]

theorem tested_current_scaled (b : Fin 3) (w : PhysicalPairSpace.Position → ℝ)
    (hw : AEStronglyMeasurable w volume) {L : ℝ} (hL : ∀ y, ‖w y‖ ≤ L) (p : Pair) :
    ∫ y, w y * currentL1 p y b = (L + 1) * spatialCurrentTest b (scaledTest w hw hL) p := by
  have hpos : L + 1 ≠ 0 := ne_of_gt (by linarith [(norm_nonneg _).trans (hL 0)])
  rw [spatialCurrentTest_eq, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  change _ = _ * (w y / (L + 1) * _)
  field_simp

theorem tested_density_scaled (w : PhysicalPairSpace.Position → ℝ)
    (hw : AEStronglyMeasurable w volume) {L : ℝ} (hL : ∀ y, ‖w y‖ ≤ L) (p : Pair) :
    ∫ y, w y * densityL1 p y = (L + 1) * spatialDensityTest (scaledTest w hw hL) p := by
  have hpos : L + 1 ≠ 0 := ne_of_gt (by linarith [(norm_nonneg _).trans (hL 0)])
  rw [spatialDensityTest_eq, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  change _ = _ * (w y / (L + 1) * _)
  field_simp

/-- Bounded tests of the current pass through pair series. -/
theorem tested_current_hasSum {p : ℕ → Pair} {q : Pair} (h : HasSum p q) (b : Fin 3)
    (w : PhysicalPairSpace.Position → ℝ) (hw : AEStronglyMeasurable w volume) {L : ℝ}
    (hL : ∀ y, ‖w y‖ ≤ L) :
    HasSum (fun n => ∫ y, w y * currentL1 (p n) y b) (∫ y, w y * currentL1 q y b) := by
  have h1 := ((spatialCurrentTest b (scaledTest w hw hL)).hasSum h).mul_left (L + 1)
  rw [← tested_current_scaled b w hw hL q] at h1
  exact hasSum_of_eq h1 fun n => (tested_current_scaled b w hw hL (p n)).symm

/-- Bounded tests of the density pass through pair series. -/
theorem tested_density_hasSum {p : ℕ → Pair} {q : Pair} (h : HasSum p q)
    (w : PhysicalPairSpace.Position → ℝ) (hw : AEStronglyMeasurable w volume) {L : ℝ}
    (hL : ∀ y, ‖w y‖ ≤ L) :
    HasSum (fun n => ∫ y, w y * densityL1 (p n) y) (∫ y, w y * densityL1 q y) := by
  have h1 := ((spatialDensityTest (scaledTest w hw hL)).hasSum h).mul_left (L + 1)
  rw [← tested_density_scaled w hw hL q] at h1
  exact hasSum_of_eq h1 fun n => (tested_density_scaled w hw hL (p n)).symm

end Tests

section Generic

variable {N : ℕ} (i : Fin N) (V : Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ b, AEStronglyMeasurable (κ b) volume)
  (M : ℝ) (hbound : ∀ b, ∀ᵐ x ∂volume, ‖κ b x‖ ≤ M)
  (e : ℝ) (W : ConcreteWeylLaw photonMeasure) {f : Lp ℂ 2 photonMeasure}
  (K : WeightedPhotonKernel)
  (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)

/-- **The current of a displaced vector**: `j_{W u} = j_u - e ρ_u c`, tested
against a bounded weight, when the classical field of the particle coordinates
is a function `c` of the particle position. -/
theorem tested_current_weylRef (b : Fin 3) (c : PhysicalPairSpace.Position → ℝ)
    (hcm : AEStronglyMeasurable c volume) {L : ℝ} (hcL : ∀ y, ‖c y‖ ≤ L)
    (hcl : ∀ z, classicalField κ f (i, b) z = c (SymmetricLift.particle z i))
    (w : PhysicalPairSpace.Position → ℝ) (hw : AEStronglyMeasurable w volume) {L' : ℝ}
    (hwL : ∀ y, ‖w y‖ ≤ L') (u : Reference (Fin N × Fin 3) V) :
    ∫ y, w y * currentL1 (PhysicalPFPairSeries.vectorPair i V C κ hκ M hbound e
        (weylRef V W K hK u)) y b =
      (∫ y, w y * currentL1 (PhysicalPFPairSeries.vectorPair i V C κ hκ M hbound e u) y b) -
        e * ∫ y, (w y * c y) *
          densityL1 (PhysicalPFPairSeries.vectorPair i V C κ hκ M hbound e u) y := by
  have hwc : AEStronglyMeasurable (fun y => w y * c y) volume := hw.mul hcm
  have hwcL : ∀ y, ‖w y * c y‖ ≤ L' * L := fun y => by
    rw [norm_mul]
    exact mul_le_mul (hwL y) (hcL y) (norm_nonneg _) ((norm_nonneg _).trans (hwL y))
  have hmw : AEStronglyMeasurable (fun z => w ((PhysicalSourceCoordinates.split i) z).1) volume :=
    hw.comp_fst.comp_measurePreserving (PhysicalSourceCoordinates.split_measurePreserving i)
  have hmwc : AEStronglyMeasurable (fun z => w ((PhysicalSourceCoordinates.split i) z).1 *
      c ((PhysicalSourceCoordinates.split i) z).1) volume :=
    hwc.comp_fst.comp_measurePreserving (PhysicalSourceCoordinates.split_measurePreserving i)
  have hi₁ : Integrable (fun z => w ((PhysicalSourceCoordinates.split i) z).1 *
      (⟪inclusion (Fin N × Fin 3) V u z,
        covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, b) u z⟫_ℂ).re) volume :=
    ((L2.integrable_inner (𝕜 := ℂ) _ _).re.congr (ae_of_all _ fun z =>
      RCLike.re_to_complex)).bdd_mul hmw (c := L') (ae_of_all _ fun z => hwL _)
  have hi₂ : Integrable (fun z => (w ((PhysicalSourceCoordinates.split i) z).1 *
      c ((PhysicalSourceCoordinates.split i) z).1) *
        ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2) volume :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp
      (Lp.memLp _)).bdd_mul hmwc (c := L' * L) (ae_of_all _ fun z => hwcL _)
  refine (PhysicalSourcePair.tested_current_ofWaveFunction i
    (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V (weylRef V W K hK u)))
    (fun a => covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, a) (weylRef V W K hK u)) b
    w hw (ae_of_all _ hwL)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (fun x y : ℝ => x - e * y)
    (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, a) u) b w hw
      (ae_of_all _ hwL)).symm
    (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, a) u) _ hwc
      (ae_of_all _ hwcL)).symm)
  refine Eq.trans ?_ (mul_sub_algebra _ _ _ _)
  refine congrArg (fun r : ℝ => (N : ℝ) * r) ?_
  refine Eq.trans ?_ ((integral_sub hi₁ (hi₂.const_mul e)).trans
    (congrArg₂ (· - ·) rfl (integral_const_mul e _)))
  refine integral_congr_ae ?_
  filter_upwards [inclusion_weylRef_ae V W K hK u,
    covariant_weylRef_ae V W K hK C κ hκ M hbound e (i, b) u] with z h₁ h₂
  change w _ * (⟪inclusion (Fin N × Fin 3) V (weylRef V W K hK u) z,
    covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, b) (weylRef V W K hK u) z⟫_ℂ).re = _
  refine (congrArg₂ (fun a d => w ((PhysicalSourceCoordinates.split i) z).1 * (⟪a, d⟫_ℂ).re)
    h₁ h₂).trans ?_
  refine (congrArg (fun r : ℝ => w ((PhysicalSourceCoordinates.split i) z).1 * r)
    (re_inner_weyl_shift (W.weyl f) _ _ _)).trans ?_
  refine (congrArg (fun r : ℝ => w ((PhysicalSourceCoordinates.split i) z).1 *
    ((⟪inclusion (Fin N × Fin 3) V u z,
      covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, b) u z⟫_ℂ).re - e * r *
        ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2)) (hcl z)).trans ?_
  exact shift_algebra w c (PhysicalSourcePair.split_fst_eq_particle i z) _ _ _

end Generic

section Physical

variable {N : ℕ} (i : Fin N) (F : PhysicalPolarization.Frame)
  (χ : PhysicalPolarization.ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (e : ℝ) (W : ConcreteWeylLaw photonMeasure)

set_option hygiene false in
local notation "Vp" => PhysicalRemoval.potential N 1
set_option hygiene false in
local notation "κF" => PhysicalRemovalKernels.full F χ N
set_option hygiene false in
local notation "hκF" => PhysicalRemovalKernels.full_measurable F χ N
set_option hygiene false in
local notation "MF" => PhysicalRemovalKernels.bound F χ
set_option hygiene false in
local notation "hbF" => PhysicalRemovalKernels.full_bound F χ N

theorem classicalVector_smul (f : Lp ℂ 2 photonMeasure) (t : ℝ) (a : Fin 3)
    (y : PhysicalPairSpace.Position) :
    classicalVector F χ ((t : ℂ) • f) a y = t * classicalVector F χ f a y := by
  unfold classicalVector
  rw [inner_smul_right, Complex.re_ofReal_mul]
  ring

/-- **The current of a displaced density matrix**, tested against a bounded weight. -/
theorem weylState_tested_current (t : ℝ) {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (m : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N)) (b : Fin 3)
    (w : PhysicalPairSpace.Position → ℝ) (hw : AEStronglyMeasurable w volume) {L' : ℝ}
    (hwL : ∀ y, ‖w y‖ ≤ L') :
    ∫ y, w y * currentL1 ((PhysicalRemoval.model i F χ 1 C B S e).density
        (weylState Vp C κF hκF MF hbF B S e W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) m)) y b =
      (∫ y, w y * currentL1 ((PhysicalRemoval.model i F χ 1 C B S e).density m) y b) -
        e * ∫ y, (w y * classicalVector F χ ((t : ℂ) • f) b y) *
          densityL1 ((PhysicalRemoval.model i F χ 1 C B S e).density m) y := by
  let s := PhysicalPFStates.source Vp C κF hκF MF hbF B S e m.val.val m.val.property.1
    m.val.property.2.2
  have hwc : AEStronglyMeasurable (fun y => w y * classicalVector F χ ((t : ℂ) • f) b y) volume :=
    hw.mul (classicalVector_continuous F χ _ b).aestronglyMeasurable
  have hwcL : ∀ y, ‖w y * classicalVector F χ ((t : ℂ) • f) b y‖ ≤
      L' * (2 * PhysicalRemovalKernels.bound F χ * ‖(t : ℂ) • f‖) := fun y => by
    rw [norm_mul]
    exact mul_le_mul (hwL y) (classicalVector_bound F χ _ b y) (norm_nonneg _)
      ((norm_nonneg _).trans (hwL y))
  have hpair := PhysicalPFSpectral.mixed_pair_hasSum i Vp C κF hκF MF hbF B S e m s
  have hW : HasSum (fun n => ∫ y, w y * currentL1 (PhysicalPFPairSeries.vectorPair i Vp C κF hκF MF
      hbF e (weylRef Vp W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) (s.vector n))) y b)
      (∫ y, w y * currentL1 ((PhysicalRemoval.model i F χ 1 C B S e).density
        (weylState Vp C κF hκF MF hbF B S e W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) m)) y b) :=
    tested_current_hasSum (weylState_pair_hasSum i Vp C κF hκF MF hbF B S e W ((t : ℂ) • K)
      (scaled_kernel hK (t : ℂ)) m s) b w hw hwL
  have hW' := hasSum_of_eq hW fun n => tested_current_weylRef i Vp C κF hκF MF hbF e W
    ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) b (classicalVector F χ ((t : ℂ) • f) b)
    (classicalVector_continuous F χ _ b).aestronglyMeasurable (classicalVector_bound F χ _ b)
    (fun z => rfl) w hw hwL (s.vector n)
  exact hW'.unique ((tested_current_hasSum hpair b w hw hwL).sub
    ((tested_density_hasSum hpair _ hwc hwcL).mul_left e))

/-- The current of a gradient pair: `j = ρ ∇S`. -/
theorem current_gradient (G : TransformationsGauge.SpatialGauge) (ρ : Density) (a : Fin 3) :
    ∀ᵐ y ∂volume, currentL1 (G.shiftPair (ρ, 0)) y a =
      densityL1 (G.shiftPair (ρ, 0)) y * G.gradient a y := by
  have h0 : currentL1 ((ρ, 0) : Pair) = 0 := by
    change (fst.comp (ContinuousLinearMap.snd ℝ Density Current)) ((ρ, 0) : Pair) = 0
    simp
  filter_upwards [G.currentL1_shiftPair (ρ, 0),
    Lp.coeFn_zero Vector 1 (volume : Measure PhysicalPairSpace.Position)] with y h₁ h₂
  rw [h₁, G.densityL1_shiftPair, h0, h₂, Pi.zero_apply, zero_add, PiLp.smul_apply,
    TransformationsGauge.SpatialGauge.gradientVector_apply, smul_eq_mul]

/-- The gauge side of the cancellation: `∫ (∂ₐ(-S) c_{tf}^a) ρ = -t ∫ c_f^a j^a` at `j = ρ ∇S`. -/
theorem gauge_term (t : ℝ) (f : Lp ℂ 2 photonMeasure) (G : TransformationsGauge.SpatialGauge)
    (ρ : Density) (a : Fin 3) :
    ∫ y, (G.neg.gradient a y * classicalVector F χ ((t : ℂ) • f) a y) *
        densityL1 (G.shiftPair (ρ, 0)) y =
      -(t * ∫ y, classicalVector F χ f a y * currentL1 (G.shiftPair (ρ, 0)) y a) := by
  refine (integral_congr_ae ?_).trans ((integral_neg _).trans
    (congrArg Neg.neg (integral_const_mul t _)))
  filter_upwards [current_gradient G ρ a] with y hy
  rw [hy, G.neg_gradient, classicalVector_smul]
  ring

/-- **The gauge energy of a displaced optimizer**: `E_g(p_{Γ_t}) = E_g(d) + e t J`
for `g = -S` at `d = (ρ, ρ ∇S)`. -/
theorem energyShift_weylState (t : ℝ) {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (G : TransformationsGauge.SpatialGauge) {ρ : Density}
    (m : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N))
    (hm : (PhysicalRemoval.model i F χ 1 C B S e).density m = G.shiftPair (ρ, 0)) :
    G.neg.energyShift ((PhysicalRemoval.model i F χ 1 C B S e).density
        (weylState Vp C κF hκF MF hbF B S e W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) m)) =
      G.neg.energyShift (G.shiftPair (ρ, 0)) +
        e * t * ∑ a, ∫ y, classicalVector F χ f a y * currentL1 (G.shiftPair (ρ, 0)) y a := by
  have hfst : ((PhysicalRemoval.model i F χ 1 C B S e).density
      (weylState Vp C κF hκF MF hbF B S e W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) m)).1 =
        (G.shiftPair (ρ, 0)).1 :=
    (weylState_density_fst i Vp C κF hκF MF hbF B S e W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ))
      m).trans (congrArg Prod.fst hm)
  have hρ : densityL1 ((PhysicalRemoval.model i F χ 1 C B S e).density
      (weylState Vp C κF hκF MF hbF B S e W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) m)) =
        densityL1 (G.shiftPair (ρ, 0)) :=
    congrArg (fun p : Density => PhysicalPairSpace.fst p) hfst
  have hcur : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      ∫ y, G.neg.gradient a y * currentL1 ((PhysicalRemoval.model i F χ 1 C B S e).density
        (weylState Vp C κF hκF MF hbF B S e W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) m)) y a =
      (∫ y, G.neg.gradient a y * currentL1 (G.shiftPair (ρ, 0)) y a) +
        e * t * ∫ y, classicalVector F χ f a y * currentL1 (G.shiftPair (ρ, 0)) y a :=
    fun a _ => by
      have h := weylState_tested_current i F χ C B S e W t K hK m a (G.neg.gradient a)
        (G.neg.gradient_measurable a).aestronglyMeasurable
        (fun y => by rw [Real.norm_eq_abs]; exact G.neg.abs_gradient_le a y)
      exact current_algebra' h
        (congrArg (fun p : Pair => ∫ y, G.neg.gradient a y * currentL1 p y a) hm)
        ((congrArg (fun p : Pair => ∫ y, (G.neg.gradient a y *
          classicalVector F χ ((t : ℂ) • f) a y) * densityL1 p y) hm).trans
            (gauge_term F χ t f G ρ a))
  have hS : (∑ a, ∫ y, G.neg.gradient a y * currentL1 ((PhysicalRemoval.model i F χ 1 C B S e).density
      (weylState Vp C κF hκF MF hbF B S e W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) m)) y a) =
      (∑ a, ∫ y, G.neg.gradient a y * currentL1 (G.shiftPair (ρ, 0)) y a) +
        e * t * ∑ a, ∫ y, classicalVector F χ f a y * currentL1 (G.shiftPair (ρ, 0)) y a := by
    rw [Finset.sum_congr rfl hcur, Finset.sum_add_distrib, Finset.mul_sum]
  have hD : (∫ x, (∑ a, G.neg.gradient a x ^ 2) * densityL1 ((PhysicalRemoval.model i F χ 1 C B S
      e).density (weylState Vp C κF hκF MF hbF B S e W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ))
        m)) x) = ∫ x, (∑ a, G.neg.gradient a x ^ 2) * densityL1 (G.shiftPair (ρ, 0)) x :=
    congrArg (fun r : Lp ℝ 1 (volume : Measure PhysicalPairSpace.Position) =>
      ∫ x, (∑ a, G.neg.gradient a x ^ 2) * r x) hρ
  exact energyShift_algebra hS hD

variable (BF : StandardSymmetricFockExponential) (BW : StandardWienerSegal)
  (core : Gaussian.CountableSpatialTestCore) (smooth : Gaussian.SmoothSobolevBackground)
  (C₀ : ℝ) (scaled : Gaussian.ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C₀)
  (B₀ : SymmetricLift.TensorBackground Repair.SixTag) (B₁ : SymmetricLift.TensorMultilinearData B₀)
  {ι : Type*} (basis : HilbertBasis ι ℂ (SymmetricLift.recursiveLiftCandidate B₀ N).target)
  (index : ι ↪ ℕ) (Sob : PhysicalSobolevRealization.StandardHomogeneousSobolev)
  (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
  (Hardy : PhysicalPhotonLocalizedNumber.StandardFractionalHardy)
  (hLp : PhysicalPairDuality.StandardFiniteDimensionalLpRepresentation)
  (hFM : PhysicalPairDuality.StandardDualFenchelMoreau)

set_option backward.isDefEq.respectTransparency.types true in
include BF BW core smooth scaled B₀ B₁ basis index in
/-- **Gauge covariance of the mixed functional** `F̃_L`, from that of `F_LL` and
`F_LL = F̃_L`. -/
theorem mixed_gauge (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) (g : TransformationsGauge.SpatialGauge)
    (d : Pair) :
    PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e (g.shiftPair d) =
      PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e d +
        ((g.energyShift d : ℝ) : EReal) := by
  have h : PhysicalAttainmentFunctionals.pureFunctional i F χ C B S e (g.shiftPair d) =
      PhysicalAttainmentFunctionals.pureFunctional i F χ C B S e d +
        ((g.energyShift d : ℝ) : EReal) :=
    g.search_gauge (PhysicalRemoval.potential N 1) C
      (PhysicalProfiles.momentumKernel (PhysicalPolarization.formFactors F χ) rfl
        (LinearIsometryEquiv.refl ℝ _))
      (PhysicalProfiles.momentumKernel_continuous (PhysicalPolarization.formFactors F χ) rfl
        (LinearIsometryEquiv.refl ℝ _))
      (PhysicalProfiles.kernelBound (PhysicalPolarization.formFactors F χ) rfl
        (LinearIsometryEquiv.refl ℝ _))
      (PhysicalProfiles.momentumKernel_bound (PhysicalPolarization.formFactors F χ) rfl
        (LinearIsometryEquiv.refl ℝ _)) e i B S d
  exact (PhysicalPureFunctional.pure_eq_mixed i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁
    basis index he hC₀ (g.shiftPair d)).symm.trans (h.trans
      (congrArg (fun r : EReal => r + ((g.energyShift d : ℝ) : EReal))
        (PhysicalPureFunctional.pure_eq_mixed i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁
          basis index he hC₀ d)))

include BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **The gauge lower bound.** If `Γ` is optimal at `(ρ, ρ ∇S)`, every density
matrix `Γ'` with density `ρ` has `Tr(H Γ) + E_g(d) ≤ Tr(H Γ') + E_g(p_{Γ'})`,
where `g = -S`. -/
theorem energy_lower_bound (he : 0 ≤ e) (hC₀ : 0 ≤ C₀) (G : TransformationsGauge.SpatialGauge)
    {ρ : Density} (m : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N))
    (hopt : ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
      PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e (G.shiftPair (ρ, 0)))
    (Γ : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N))
    (hΓ : ((PhysicalRemoval.model i F χ 1 C B S e).density Γ).1 = ρ) :
    (PhysicalRemoval.model i F χ 1 C B S e).energy m + G.neg.energyShift (G.shiftPair (ρ, 0)) ≤
      (PhysicalRemoval.model i F χ 1 C B S e).energy Γ +
        G.neg.energyShift ((PhysicalRemoval.model i F χ 1 C B S e).density Γ) := by
  have hcov := fun q => mixed_gauge i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index
    he hC₀ G.neg q
  have hzc := (PhysicalZeroCurrent.zero_current_density_functional i F χ C B S e BF BW core smooth
    C₀ scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM he hC₀ ρ).2.1
  have hF0 : PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e (ρ, 0) =
      (((PhysicalRemoval.model i F χ 1 C B S e).energy m +
        G.neg.energyShift (G.shiftPair (ρ, 0)) : ℝ) : EReal) :=
    (congrArg (PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e)
      (G.neg_shiftPair (ρ, 0))).symm.trans ((hcov (G.shiftPair (ρ, 0))).trans
        ((congrArg (fun r : EReal => r + ((G.neg.energyShift (G.shiftPair (ρ, 0)) : ℝ) : EReal))
          hopt.symm).trans (EReal.coe_add _ _).symm))
  have hfst : (G.neg.shiftPair ((PhysicalRemoval.model i F χ 1 C B S e).density Γ)).1 = ρ :=
    (ext_ae (Filter.EventuallyEq.of_eq (congrArg
      (fun g : Lp ℝ 1 volume => (g : PhysicalPairSpace.Position → ℝ))
      (G.neg.densityL1_shiftPair _)))).trans hΓ
  have hdens : PhysicalZeroCurrent.densityMixedFunctional i F χ C B S e ρ ≤
      PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e
        (G.neg.shiftPair ((PhysicalRemoval.model i F χ 1 C B S e).density Γ)) :=
    le_iInf₂ fun Γ' hΓ' => (iInf₂_le Γ' ((congrArg Prod.fst hΓ').trans hfst)).trans_eq
      (PhysicalAttainmentFunctionals.mixedModel_energy_coe i F χ C B S e Γ').symm
  refine EReal.coe_le_coe_iff.mp ?_
  exact hF0.symm.trans_le (hzc.trans_le (hdens.trans
    ((hcov ((PhysicalRemoval.model i F χ 1 C B S e).density Γ)).trans_le
      ((add_le_add (DFT.search_le (PhysicalRemoval.model i F χ 1 C B S e) (s := Γ) rfl)
        le_rfl).trans_eq (EReal.coe_add _ _).symm))))

include W BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **No real linear response at a gradient current.** -/
theorem optimizer_gradient_current_re (he : 0 ≤ e) (hC₀ : 0 ≤ C₀)
    (G : TransformationsGauge.SpatialGauge)
    (m : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N)) {ρ : Density}
    (hm : (PhysicalRemoval.model i F χ 1 C B S e).density m = G.shiftPair (ρ, 0))
    (hopt : ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
      PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e (G.shiftPair (ρ, 0)))
    {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (s : PhysicalPFSource.SupportedSource N (PhysicalRemoval.potential N 1) B m.val.val) :
    ∑' n, (⟪annihilationRef (PhysicalRemoval.potential N 1) K (s.vector n),
      inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) (s.vector n)⟫_ℂ).re = 0 := by
  have he' := m.val.property.2.2
  have hE : HasSum (fun n => energy (Fin N × Fin 3) Vp C κF hκF MF hbF e (s.vector n))
      ((PhysicalRemoval.model i F χ 1 C B S e).energy m) :=
    s.energy_hasSum C κF hκF MF hbF S e he'
  have hM := source_mass_one Vp C κF hκF MF hbF B S e m s.toSource
  have hA := Complex.hasSum_re (amplitude_summable Vp C κF hκF MF hbF B S e s.toSource he' K).hasSum
  have hQs : Summable (fun n => densityShift Vp κF f (s.vector n)) :=
    Summable.of_nonneg_of_le (fun n => densityShift_nonneg _ _ f _)
      (fun n => densityShift_le _ _ _ hbF f _) (hM.summable.mul_left _)
  have hQ := hQs.hasSum
  have hJ := currentShift_hasSum i F χ C B S e f m s
  have hJd := congrArg (fun p : Pair => ∑ a, ∫ y, classicalVector F χ f a y * currentL1 p y a) hm
  have hshift : (G.shiftPair (ρ, 0)).1 = ρ :=
    ext_ae (Filter.EventuallyEq.of_eq (congrArg
      (fun g : Lp ℝ 1 volume => (g : PhysicalPairSpace.Position → ℝ))
      (G.densityL1_shiftPair (ρ, 0))))
  have hcurve : ∀ t : ℝ, 0 ≤ 2 * t * (∑' n, ⟪annihilationRef Vp K (s.vector n),
      inclusion (Fin N × Fin 3) Vp (s.vector n)⟫_ℂ).re +
      t ^ 2 * (‖K.val.2‖ ^ 2 + e ^ 2 / 2 * ∑' n, densityShift Vp κF f (s.vector n)) := by
    intro t
    have h1 := weylState_energy_hasSum i Vp C κF hκF MF hbF B S e W ((t : ℂ) • K)
      (scaled_kernel hK (t : ℂ)) m s.toSource
    have h1' := hasSum_of_eq h1 fun n => energy_scaled Vp C κF hκF MF hbF e W t K hK (s.vector n)
    have h2 := ((hE.add ((hA.mul_left t).mul_left 2)).add
      (hM.mul_left (t ^ 2 * ‖K.val.2‖ ^ 2))).add
        ((hJ.mul_left (-(e * t))).add (hQ.mul_left (e ^ 2 * t ^ 2 / 2)))
    have heq := h1'.unique h2
    have hX := energyShift_weylState i F χ C B S e W t K hK G m hm
    have hle := energy_lower_bound i F χ C B S e BF BW core smooth C₀ scaled B₀ B₁ basis index
      Sob Rellich Hardy hLp hFM he hC₀ G m hopt
      (weylState Vp C κF hκF MF hbF B S e W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) m)
      ((weylState_density_fst i Vp C κF hκF MF hbF B S e W ((t : ℂ) • K)
        (scaled_kernel hK (t : ℂ)) m).trans ((congrArg Prod.fst hm).trans hshift))
    exact curve_gauge heq hJd hle hX
  have hb : 0 ≤ ‖K.val.2‖ ^ 2 + e ^ 2 / 2 * ∑' n, densityShift Vp κF f (s.vector n) :=
    add_nonneg (sq_nonneg _) (mul_nonneg (by positivity)
      (tsum_nonneg fun n => densityShift_nonneg _ _ f _))
  exact hA.tsum_eq.trans (linear_coefficient_zero hb hcurve)

include W BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- Coherent amplitudes in `D(ω)` vanish at a gradient current. -/
theorem optimizer_gradient_current_amplitude (he : 0 ≤ e) (hC₀ : 0 ≤ C₀)
    (G : TransformationsGauge.SpatialGauge)
    (m : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N)) {ρ : Density}
    (hm : (PhysicalRemoval.model i F χ 1 C B S e).density m = G.shiftPair (ρ, 0))
    (hopt : ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
      PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e (G.shiftPair (ρ, 0)))
    {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (s : PhysicalPFSource.SupportedSource N (PhysicalRemoval.potential N 1) B m.val.val) :
    sourceAmplitude (PhysicalRemoval.potential N 1) B s.toSource K = 0 := by
  have hre := optimizer_gradient_current_re i F χ C B S e W BF BW core smooth C₀ scaled B₀ B₁
    basis index Sob Rellich Hardy hLp hFM he hC₀ G m hm hopt K hK s
  have him := optimizer_gradient_current_re i F χ C B S e W BF BW core smooth C₀ scaled B₀ B₁
    basis index Sob Rellich Hardy hLp hFM he hC₀ G m hm hopt (Complex.I • K)
    (scaled_kernel hK Complex.I) s
  have hs := sourceAmplitude_summable Vp C κF hκF MF hbF B S e s.toSource m.val.property.2.2 K
  apply Complex.ext
  · refine (Complex.hasSum_re hs.hasSum).tsum_eq.symm.trans ?_
    refine (tsum_congr fun n => re_inner_comm _ _).trans ?_
    exact hre.trans Complex.zero_re.symm
  · refine (Complex.hasSum_im hs.hasSum).tsum_eq.symm.trans ?_
    refine (tsum_congr fun n => amplitude_I Vp K (s.vector n)).trans ?_
    exact him.trans Complex.zero_im.symm

include W BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **Every coherent amplitude of an optimizer at a gradient current vanishes**:
at `(ρ, ρ ∇S)` with `∇S` bounded, `Tr(a(h) Γ) = 0` for every `h` with
`h/√ω ∈ L²`, in every fermionic spectral source. -/
theorem optimizer_gradient_current_weighted (he : 0 ≤ e) (hC₀ : 0 ≤ C₀)
    (G : TransformationsGauge.SpatialGauge)
    (m : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N)) {ρ : Density}
    (hm : (PhysicalRemoval.model i F χ 1 C B S e).density m = G.shiftPair (ρ, 0))
    (hopt : ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
      PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e (G.shiftPair (ρ, 0)))
    (k : WeightedPhotonKernel)
    (s : PhysicalPFSource.SupportedSource N (PhysicalRemoval.potential N 1) B m.val.val) :
    sourceAmplitude (PhysicalRemoval.potential N 1) B s.toSource k = 0 :=
  sourceAmplitude_eq_zero_of_trunc Vp C κF hκF MF hbF B S e s.toSource m.val.property.2.2 k
    fun n => optimizer_gradient_current_amplitude i F χ C B S e W BF BW core smooth C₀ scaled B₀
      B₁ basis index Sob Rellich Hardy hLp hFM he hC₀ G m hm hopt (truncKernel n k)
      (truncKernel_direction n k) s

include W BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **The mean vector potential and the mean magnetic field of an optimizer at a
gradient current vanish**: at `(ρ, ρ ∇S)` with `∇S` bounded, `Tr(A(y) Γ) = 0` at
every point, and `∫ g · Tr(A Γ) = 0` for every vector field `g`, in particular
for `g = ∇ × v`. -/
theorem optimizer_gradient_current_fields (he : 0 ≤ e) (hC₀ : 0 ≤ C₀)
    (G : TransformationsGauge.SpatialGauge)
    (m : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N)) {ρ : Density}
    (hm : (PhysicalRemoval.model i F χ 1 C B S e).density m = G.shiftPair (ρ, 0))
    (hopt : ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
      PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e (G.shiftPair (ρ, 0)))
    (s : PhysicalPFSource.SupportedSource N (PhysicalRemoval.potential N 1) B m.val.val) :
    (∀ a y, meanVectorPotential F χ B s.toSource a y = 0) ∧
      ∀ g : PhysicalPairSpace.Position → Vector,
        ∫ y, ∑ a, g y a * meanVectorPotential F χ B s.toSource a y = 0 := by
  have h : ∀ a y, meanVectorPotential F χ B s.toSource a y = 0 := fun a y => by
    unfold meanVectorPotential
    rw [optimizer_gradient_current_weighted i F χ C B S e W BF BW core smooth C₀ scaled B₀ B₁
      basis index Sob Rellich Hardy hLp hFM he hC₀ G m hm hopt _ s, Complex.zero_re, mul_zero]
  refine ⟨h, fun g => ?_⟩
  simp only [h, mul_zero, Finset.sum_const_zero, integral_zero]

end Physical

end GptLean.PhysicalWeyl
