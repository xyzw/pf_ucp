import GptLean.PhysicalMeanFields
import GptLean.PhysicalZeroCurrent
import GptLean.PhysicalPFParticle

/-!
`prop-optimizer-mean-fields` (iii) at zero current: coherent amplitudes of
optimizers at `(ρ, 0)` vanish for every direction in `D(ω)`.

Let `Γ` minimize the energy at `(ρ, 0)` and let `f` satisfy `√ω f, ω f ∈ L²`.
The displaced states `Γ_t = W(t f) Γ W(t f)†` have density `ρ` (their current
changes). For a fermionic spectral source `Γ = ∑ₙ |uₙ⟩⟨uₙ|`,

`E(Γ_t) = E(Γ) + 2t Re Tr(a(ω f) Γ) + t² ‖√ω f‖² - e t ∫ c_f · j_Γ + (e² t² / 2) Q`,

with `Q ≥ 0`, where `c_f(y) = 2 Re ⟨G_y, f⟩` is the classical field of `f`. The
current term vanishes because `j_Γ = 0`. By `zero-current-density-search`, `Γ`
also minimizes the energy among all density matrices with density `ρ`, so the
linear coefficient vanishes. Using `f` and `i f` gives `Tr(a(ω f) Γ) = 0`.
-/

noncomputable section

namespace GptLean.PhysicalWeyl

open MeasureTheory Filter PhysicalFock PhysicalPFReference PhysicalPFSoftTag
  PhysicalNormalTrace PhysicalPairSpace Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem re_inner_comm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a b : E) :
    (⟪a, b⟫_ℂ).re = (⟪b, a⟫_ℂ).re := by
  rw [← inner_conj_symm, Complex.conj_re]

theorem half_sum_algebra {ι : Type*} (s : Finset ι) (J Q : ι → ℝ) (e t : ℝ) :
    (1 / 2 : ℝ) * ∑ b ∈ s, (-(2 * e * (t * J b)) + e ^ 2 * (t ^ 2 * Q b)) =
      -(e * t) * ∑ b ∈ s, J b + (e ^ 2 * t ^ 2 / 2) * ∑ b ∈ s, Q b := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem hasSum_of_eq {f g : ℕ → ℝ} {a : ℝ} (h : HasSum f a) (hfg : ∀ n, f n = g n) :
    HasSum g a :=
  (funext hfg) ▸ h

theorem sum_const_mul {ι : Type*} [Fintype ι] (a n : ℝ) :
    ∑ _b : ι, a * n = Fintype.card ι * a * n := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- The last step of the zero-current curve argument, over the reals. -/
theorem curve_zero {E E' A Kn Q J t e : ℝ}
    (heq : E' = E + 2 * (t * A) + t ^ 2 * Kn * 1 + (-(e * t) * J + e ^ 2 * t ^ 2 / 2 * Q))
    (hJ : J = 0) (hle : E ≤ E') : 0 ≤ 2 * t * A + t ^ 2 * (Kn + e ^ 2 / 2 * Q) := by
  have h : 2 * t * A + t ^ 2 * (Kn + e ^ 2 / 2 * Q) = E' - E := by
    rw [heq, hJ]
    ring
  rw [h]
  exact sub_nonneg.mpr hle

theorem energy_scaled_algebra {ι : Type*} (s : Finset ι) (E A A' Kn Kn' n e t : ℝ)
    (J J' Q Q' : ι → ℝ) (hA : A' = t * A) (hK : Kn' = t ^ 2 * Kn)
    (hJ : ∀ b, J' b = t * J b) (hQ : ∀ b, Q' b = t ^ 2 * Q b) :
    E + 2 * A' + Kn' * n + (1 / 2 : ℝ) * ∑ b ∈ s, (-(2 * e * J' b) + e ^ 2 * Q' b) =
      E + 2 * (t * A) + t ^ 2 * Kn * n +
        (-(e * t) * ∑ b ∈ s, J b + (e ^ 2 * t ^ 2 / 2) * ∑ b ∈ s, Q b) := by
  have hs : ∑ b ∈ s, (-(2 * e * J' b) + e ^ 2 * Q' b) =
      ∑ b ∈ s, (-(2 * e * (t * J b)) + e ^ 2 * (t ^ 2 * Q b)) :=
    Finset.sum_congr rfl fun b _ => by rw [hJ b, hQ b]
  rw [hA, hK, hs, half_sum_algebra]

section Generic

variable {N : ℕ} (i : Fin N) (V : Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ b, AEStronglyMeasurable (κ b) volume)
  (M : ℝ) (hbound : ∀ b, ∀ᵐ x ∂volume, ‖κ b x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (e : ℝ) (W : ConcreteWeylLaw photonMeasure)

/-- The current coupling `J(u) = ∑_b ∫ c_b Re ⟨D_b u, u⟩` of a displacement. -/
def currentShift (f : Lp ℂ 2 photonMeasure) (u : Reference (Fin N × Fin 3) V) : ℝ :=
  ∑ b, ∫ x, classicalField κ f b x *
    (⟪covariant (Fin N × Fin 3) V C κ hκ M hbound e b u x, inclusion (Fin N × Fin 3) V u x⟫_ℂ).re

/-- The density coupling `Q(u) = ∑_b ∫ c_b² |u|²` of a displacement. -/
def densityShift (f : Lp ℂ 2 photonMeasure) (u : Reference (Fin N × Fin 3) V) : ℝ :=
  ∑ b, ∫ x, classicalField κ f b x ^ 2 * ‖inclusion (Fin N × Fin 3) V u x‖ ^ 2

theorem integral_classicalField_smul (f : Lp ℂ 2 photonMeasure) (t : ℝ) (b : Fin N × Fin 3)
    (g : Position (Fin N × Fin 3) → ℝ) :
    ∫ x, classicalField κ ((t : ℂ) • f) b x * g x = t * ∫ x, classicalField κ f b x * g x := by
  simp only [classicalField_smul, mul_assoc]
  exact integral_const_mul t _

theorem integral_classicalField_sq_smul (f : Lp ℂ 2 photonMeasure) (t : ℝ) (b : Fin N × Fin 3)
    (g : Position (Fin N × Fin 3) → ℝ) :
    ∫ x, classicalField κ ((t : ℂ) • f) b x ^ 2 * g x =
      t ^ 2 * ∫ x, classicalField κ f b x ^ 2 * g x := by
  simp only [classicalField_smul, mul_pow, mul_assoc]
  exact integral_const_mul (t ^ 2) _

/-- **Energy along a displacement line**, general direction. -/
theorem energy_scaled (t : ℝ) {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (u : Reference (Fin N × Fin 3) V) :
    energy (Fin N × Fin 3) V C κ hκ M hbound e
        (weylRef V W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) u) =
      energy (Fin N × Fin 3) V C κ hκ M hbound e u +
        2 * (t * (⟪annihilationRef V K u, inclusion (Fin N × Fin 3) V u⟫_ℂ).re) +
        t ^ 2 * ‖K.val.2‖ ^ 2 * ‖inclusion (Fin N × Fin 3) V u‖ ^ 2 +
        (-(e * t) * currentShift V C κ hκ M hbound e f u +
          (e ^ 2 * t ^ 2 / 2) * densityShift V κ f u) := by
  exact (energy_weylRef V W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) C κ hκ M hbound e u).trans
    (energy_scaled_algebra Finset.univ _ _ _ _ _ _ e t _ _ _ _ (amplitude_scaled V t K u)
      (kernel_scaled_norm_sq t K)
      (fun b => integral_classicalField_smul κ f t b _)
      (fun b => integral_classicalField_sq_smul κ f t b _))

theorem densityShift_nonneg (f : Lp ℂ 2 photonMeasure) (u : Reference (Fin N × Fin 3) V) :
    0 ≤ densityShift V κ f u :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

include hbound in
theorem densityShift_le (f : Lp ℂ 2 photonMeasure) (u : Reference (Fin N × Fin 3) V) :
    densityShift V κ f u ≤
      Fintype.card (Fin N × Fin 3) * (2 * M * ‖f‖) ^ 2 * ‖inclusion (Fin N × Fin 3) V u‖ ^ 2 := by
  have hb : ∀ b, ∫ x, classicalField κ f b x ^ 2 * ‖inclusion (Fin N × Fin 3) V u x‖ ^ 2 ≤
      (2 * M * ‖f‖) ^ 2 * ‖inclusion (Fin N × Fin 3) V u‖ ^ 2 := fun b => by
    have hle : ∀ᵐ x ∂volume, classicalField κ f b x ^ 2 * ‖inclusion (Fin N × Fin 3) V u x‖ ^ 2 ≤
        (2 * M * ‖f‖) ^ 2 * ‖inclusion (Fin N × Fin 3) V u x‖ ^ 2 := by
      filter_upwards [classicalField_bound κ M hbound f b] with x hx
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [Real.norm_eq_abs] at hx
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    exact (integral_mono_of_nonneg (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      ((integrable_norm_sq (inclusion (Fin N × Fin 3) V u)).const_mul _) hle).trans_eq
        ((integral_const_mul _ _).trans (congrArg (fun r : ℝ => (2 * M * ‖f‖) ^ 2 * r)
          (norm_sq_eq_integral (inclusion (Fin N × Fin 3) V u)).symm))
  calc densityShift V κ f u
      ≤ ∑ _b : Fin N × Fin 3, (2 * M * ‖f‖) ^ 2 * ‖inclusion (Fin N × Fin 3) V u‖ ^ 2 :=
        Finset.sum_le_sum fun b _ => hb b
    _ = _ := sum_const_mul _ _

/-- A displacement keeps the density of every reference vector. -/
theorem densityL1_vectorPair_weylRef {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (u : Reference (Fin N × Fin 3) V) :
    densityL1 (PhysicalPFPairSeries.vectorPair i V C κ hκ M hbound e (weylRef V W K hK u)) =
      densityL1 (PhysicalPFPairSeries.vectorPair i V C κ hκ M hbound e u) := by
  apply Lp.ext
  apply RemovalConstraints.ae_eq_of_boundedSpatialTests (density_integrable _) (density_integrable _)
  intro t
  refine (PhysicalSourcePair.tested_density_ofWaveFunction i
    (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V (weylRef V W K hK u)))
    (fun a => covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, a) (weylRef V W K hK u))
    t.weight t.measurable (ae_of_all _ t.bounded)).trans (Eq.trans ?_
      (PhysicalSourcePair.tested_density_ofWaveFunction i
        (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
        (fun a => covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, a) u)
        t.weight t.measurable (ae_of_all _ t.bounded)).symm)
  refine congrArg (fun r : ℝ => (N : ℝ) * r) (integral_congr_ae ?_)
  filter_upwards [inclusion_weylRef_ae V W K hK u] with z hz
  exact congrArg (fun r : ℝ => t.weight ((PhysicalSourceCoordinates.split i) z).1 * r ^ 2)
    ((congrArg norm hz).trans (LinearIsometryEquiv.norm_map _ _))

/-- **A displacement keeps the density of a density matrix.** -/
theorem weylState_density_fst {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (m : PhysicalPFStates.MixedState V C κ hκ M hbound B S e) :
    ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density
        (weylState V C κ hκ M hbound B S e W K hK m)).1 =
      ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density m).1 := by
  let s := PhysicalPFStates.source V C κ hκ M hbound B S e m.val.val m.val.property.1
    m.val.property.2.2
  have h1 := densityL1.hasSum (weylState_pair_hasSum i V C κ hκ M hbound B S e W K hK m s)
  have h2 := densityL1.hasSum (PhysicalPFSpectral.mixed_pair_hasSum i V C κ hκ M hbound B S e m s)
  simp only [densityL1_vectorPair_weylRef i V C κ hκ M hbound e W K hK] at h1
  exact ext_ae (Filter.EventuallyEq.of_eq (congrArg (fun g : Lp ℝ 1 volume => (g : Position → ℝ))
    (h1.unique h2)))

end Generic

section Physical

variable {N : ℕ} (i : Fin N) (F : PhysicalPolarization.Frame)
  (χ : PhysicalPolarization.ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (e : ℝ) (W : ConcreteWeylLaw photonMeasure)

/-- The article's field kernels `G^a_y`. -/
abbrev fieldKernel : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel :=
  PhysicalProfiles.momentumKernel (PhysicalPolarization.formFactors F χ) rfl
    (LinearIsometryEquiv.refl ℝ _)

/-- The classical field `c_f^a(y) = 2 Re ⟨G^a_y, f⟩`. -/
def classicalVector (f : Lp ℂ 2 photonMeasure) (a : Fin 3) (y : Position) : ℝ :=
  2 * (⟪(fieldKernel F χ (a, y)).val.1, f⟫_ℂ).re

theorem classicalVector_continuous (f : Lp ℂ 2 photonMeasure) (a : Fin 3) :
    Continuous (classicalVector F χ f a) := by
  have hk := PhysicalProfiles.momentumKernel_continuous (PhysicalPolarization.formFactors F χ) rfl
    (LinearIsometryEquiv.refl ℝ _)
  exact continuous_const.mul (Complex.continuous_re.comp
    (((continuous_fst.comp continuous_subtype_val).comp
      (hk.comp (continuous_const.prodMk continuous_id))).inner continuous_const))

theorem classicalVector_bound (f : Lp ℂ 2 photonMeasure) (a : Fin 3) (y : Position) :
    ‖classicalVector F χ f a y‖ ≤ 2 * PhysicalRemovalKernels.bound F χ * ‖f‖ := by
  unfold classicalVector
  rw [Real.norm_eq_abs, abs_mul, abs_two]
  have h1 : |(⟪(fieldKernel F χ (a, y)).val.1, f⟫_ℂ).re| ≤ ‖(fieldKernel F χ (a, y)).val.1‖ * ‖f‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have h2 : ‖(fieldKernel F χ (a, y)).val.1‖ ≤ PhysicalRemovalKernels.bound F χ :=
    (_root_.norm_fst_le _).trans (PhysicalProfiles.momentumKernel_bound
      (PhysicalPolarization.formFactors F χ) rfl (LinearIsometryEquiv.refl ℝ _) (a, y))
  nlinarith [norm_nonneg f, norm_nonneg (fieldKernel F χ (a, y)).val.1]

/-- The classical field rescaled into a bounded spatial test. -/
def classicalTest (f : Lp ℂ 2 photonMeasure) (a : Fin 3) : SpatialTest where
  weight y := classicalVector F χ f a y / (2 * PhysicalRemovalKernels.bound F χ * ‖f‖ + 1)
  measurable := ((classicalVector_continuous F χ f a).div_const _).aestronglyMeasurable
  bounded y := by
    have hpos : 0 < 2 * PhysicalRemovalKernels.bound F χ * ‖f‖ + 1 := by
      have := (norm_nonneg _).trans (classicalVector_bound F χ f a y)
      linarith
    rw [norm_div, Real.norm_of_nonneg hpos.le, div_le_one hpos]
    linarith [classicalVector_bound F χ f a y]

theorem classical_current_eq (f : Lp ℂ 2 photonMeasure) (a : Fin 3) (p : Pair) :
    ∫ y, classicalVector F χ f a y * currentL1 p y a =
      (2 * PhysicalRemovalKernels.bound F χ * ‖f‖ + 1) *
        spatialCurrentTest a (classicalTest F χ f a) p := by
  have hpos : 2 * PhysicalRemovalKernels.bound F χ * ‖f‖ + 1 ≠ 0 := by
    have := (norm_nonneg _).trans (classicalVector_bound F χ f a 0)
    exact ne_of_gt (by linarith)
  rw [spatialCurrentTest_eq, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  change _ = _ * (classicalVector F χ f a y / _ * _)
  field_simp

/-- **The current coupling is the classical field tested against the current.** -/
theorem currentShift_eq (f : Lp ℂ 2 photonMeasure)
    (u : Reference (Fin N × Fin 3) (PhysicalRemoval.potential N 1))
    (hu : inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    currentShift (PhysicalRemoval.potential N 1) C (PhysicalRemovalKernels.full F χ N)
        (PhysicalRemovalKernels.full_measurable F χ N) (PhysicalRemovalKernels.bound F χ)
        (PhysicalRemovalKernels.full_bound F χ N) e f u =
      ∑ a, ∫ y, classicalVector F χ f a y *
        currentL1 (PhysicalPFPairSeries.vectorPair i (PhysicalRemoval.potential N 1) C
          (PhysicalRemovalKernels.full F χ N) (PhysicalRemovalKernels.full_measurable F χ N)
          (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.full_bound F χ N) e u) y a := by
  unfold currentShift
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin N)), Integrable (fun x =>
      classicalField (PhysicalRemovalKernels.full F χ N) f (j, a) x *
        (⟪covariant (Fin N × Fin 3) (PhysicalRemoval.potential N 1) C
          (PhysicalRemovalKernels.full F χ N) (PhysicalRemovalKernels.full_measurable F χ N)
          (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.full_bound F χ N) e (j, a) u x,
          inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) u x⟫_ℂ).re) volume :=
    fun j _ => (L2.integrable_inner (𝕜 := ℂ) _ _).re.bdd_mul
      (classicalField_aestronglyMeasurable _ (PhysicalRemovalKernels.full_measurable F χ N) f (j, a))
      (classicalField_bound _ _ (PhysicalRemovalKernels.full_bound F χ N) f (j, a))
  refine (integral_finsetSum _ hint).symm.trans (Eq.trans ?_
    (PhysicalPFParticle.pair_tested_current C (fieldKernel F χ)
      (PhysicalProfiles.momentumKernel_continuous (PhysicalPolarization.formFactors F χ) rfl
        (LinearIsometryEquiv.refl ℝ _)) (PhysicalRemovalKernels.bound F χ)
      (PhysicalProfiles.momentumKernel_bound (PhysicalPolarization.formFactors F χ) rfl
        (LinearIsometryEquiv.refl ℝ _)) (PhysicalRemoval.potential N 1) i e u hu a
      (classicalVector F χ f a) (classicalVector_continuous F χ f a).measurable
      (classicalVector_bound F χ f a)).symm)
  refine integral_congr_ae (ae_of_all _ fun z => Finset.sum_congr rfl fun j _ => ?_)
  exact congrArg (fun r : ℝ => classicalVector F χ f a (SymmetricLift.particle z j) * r) (re_inner_comm _ _)

/-- The current series of a fermionic spectral source. -/
theorem currentShift_hasSum (f : Lp ℂ 2 photonMeasure)
    (m : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N))
    (s : PhysicalPFSource.SupportedSource N (PhysicalRemoval.potential N 1) B m.val.val) :
    HasSum (fun n => currentShift (PhysicalRemoval.potential N 1) C
        (PhysicalRemovalKernels.full F χ N) (PhysicalRemovalKernels.full_measurable F χ N)
        (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.full_bound F χ N) e f
        (s.vector n))
      (∑ a, ∫ y, classicalVector F χ f a y *
        currentL1 ((PhysicalRemoval.model i F χ 1 C B S e).density m) y a) := by
  have hpair := PhysicalPFSpectral.mixed_pair_hasSum i (PhysicalRemoval.potential N 1) C
    (PhysicalRemovalKernels.full F χ N) (PhysicalRemovalKernels.full_measurable F χ N)
    (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.full_bound F χ N) B S e m s.toSource
  have hf : (fun n => currentShift (PhysicalRemoval.potential N 1) C
      (PhysicalRemovalKernels.full F χ N) (PhysicalRemovalKernels.full_measurable F χ N)
      (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.full_bound F χ N) e f
      (s.vector n)) = fun n => ∑ a, ∫ y, classicalVector F χ f a y *
        currentL1 (PhysicalPFPairSeries.vectorPair i (PhysicalRemoval.potential N 1) C
          (PhysicalRemovalKernels.full F χ N) (PhysicalRemovalKernels.full_measurable F χ N)
          (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.full_bound F χ N) e
          (s.vector n)) y a :=
    funext fun n => currentShift_eq i F χ C e f (s.vector n) (s.fermionic n)
  rw [hf]
  simp only [classical_current_eq F χ f]
  exact hasSum_sum fun a _ =>
    ((spatialCurrentTest a (classicalTest F χ f a)).hasSum hpair).mul_left _

theorem classical_current_zero (f : Lp ℂ 2 photonMeasure) (ρ : Density) :
    ∑ a, ∫ y, classicalVector F χ f a y * currentL1 ((ρ, 0) : Pair) y a = 0 := by
  have h0 : currentL1 ((ρ, 0) : Pair) = 0 := by
    change (fst.comp (ContinuousLinearMap.snd ℝ Density Current)) ((ρ, 0) : Pair) = 0
    simp
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [h0]
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [Lp.coeFn_zero Vector 1 (volume : Measure Position)] with y hy
  rw [hy]
  simp

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

include W BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **No real linear response at zero current.** -/
theorem optimizer_zero_current_re (he : 0 ≤ e) (hC₀ : 0 ≤ C₀)
    (m : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N)) {ρ : Density}
    (hm : (PhysicalRemoval.model i F χ 1 C B S e).density m = (ρ, 0))
    (hopt : ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
      PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e (ρ, 0))
    {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (s : PhysicalPFSource.SupportedSource N (PhysicalRemoval.potential N 1) B m.val.val) :
    ∑' n, (⟪annihilationRef (PhysicalRemoval.potential N 1) K (s.vector n),
      inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) (s.vector n)⟫_ℂ).re = 0 := by
  have hzc := (PhysicalZeroCurrent.zero_current_density_functional i F χ C B S e BF BW core smooth
    C₀ scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM he hC₀ ρ).2.1
  have he' := m.val.property.2.2
  have hE : HasSum (fun n => energy (Fin N × Fin 3) (PhysicalRemoval.potential N 1) C
      (PhysicalRemovalKernels.full F χ N) (PhysicalRemovalKernels.full_measurable F χ N)
      (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.full_bound F χ N) e (s.vector n))
      ((PhysicalRemoval.model i F χ 1 C B S e).energy m) :=
    s.energy_hasSum C (PhysicalRemovalKernels.full F χ N)
      (PhysicalRemovalKernels.full_measurable F χ N) (PhysicalRemovalKernels.bound F χ)
      (PhysicalRemovalKernels.full_bound F χ N) S e he'
  have hM := source_mass_one (PhysicalRemoval.potential N 1) C (PhysicalRemovalKernels.full F χ N)
    (PhysicalRemovalKernels.full_measurable F χ N) (PhysicalRemovalKernels.bound F χ)
    (PhysicalRemovalKernels.full_bound F χ N) B S e m s.toSource
  have hA := Complex.hasSum_re (amplitude_summable (PhysicalRemoval.potential N 1) C
    (PhysicalRemovalKernels.full F χ N) (PhysicalRemovalKernels.full_measurable F χ N)
    (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.full_bound F χ N) B S e
    s.toSource he' K).hasSum
  have hQs : Summable (fun n => densityShift (PhysicalRemoval.potential N 1)
      (PhysicalRemovalKernels.full F χ N) f (s.vector n)) :=
    Summable.of_nonneg_of_le (fun n => densityShift_nonneg _ _ f _)
      (fun n => densityShift_le _ _ _ (PhysicalRemovalKernels.full_bound F χ N) f _)
      (hM.summable.mul_left _)
  have hQ := hQs.hasSum
  have hJ := currentShift_hasSum i F χ C B S e f m s
  have hJ0 : (∑ a, ∫ y, classicalVector F χ f a y *
      currentL1 ((PhysicalRemoval.model i F χ 1 C B S e).density m) y a) = 0 :=
    (congrArg (fun p : Pair => ∑ a, ∫ y, classicalVector F χ f a y * currentL1 p y a) hm).trans
      (classical_current_zero F χ f ρ)
  have hcurve : ∀ t : ℝ, 0 ≤ 2 * t * (∑' n, ⟪annihilationRef (PhysicalRemoval.potential N 1) K
      (s.vector n), inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1) (s.vector n)⟫_ℂ).re +
      t ^ 2 * (‖K.val.2‖ ^ 2 + e ^ 2 / 2 * ∑' n, densityShift (PhysicalRemoval.potential N 1)
        (PhysicalRemovalKernels.full F χ N) f (s.vector n)) := by
    intro t
    have h1 := weylState_energy_hasSum i (PhysicalRemoval.potential N 1) C
      (PhysicalRemovalKernels.full F χ N) (PhysicalRemovalKernels.full_measurable F χ N)
      (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.full_bound F χ N) B S e W
      ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) m s.toSource
    have h1' := hasSum_of_eq h1 fun n => energy_scaled (PhysicalRemoval.potential N 1) C
      (PhysicalRemovalKernels.full F χ N) (PhysicalRemovalKernels.full_measurable F χ N)
      (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.full_bound F χ N) e W t K hK
      (s.vector n)
    have h2 := ((hE.add ((hA.mul_left t).mul_left 2)).add
      (hM.mul_left (t ^ 2 * ‖K.val.2‖ ^ 2))).add
        ((hJ.mul_left (-(e * t))).add (hQ.mul_left (e ^ 2 * t ^ 2 / 2)))
    have heq := h1'.unique h2
    have hden : ((PhysicalRemoval.model i F χ 1 C B S e).density
        (weylState (PhysicalRemoval.potential N 1) C (PhysicalRemovalKernels.full F χ N)
          (PhysicalRemovalKernels.full_measurable F χ N) (PhysicalRemovalKernels.bound F χ)
          (PhysicalRemovalKernels.full_bound F χ N) B S e W ((t : ℂ) • K)
          (scaled_kernel hK (t : ℂ)) m)).1 = ρ :=
      (weylState_density_fst i (PhysicalRemoval.potential N 1) C (PhysicalRemovalKernels.full F χ N)
        (PhysicalRemovalKernels.full_measurable F χ N) (PhysicalRemovalKernels.bound F χ)
        (PhysicalRemovalKernels.full_bound F χ N) B S e W ((t : ℂ) • K)
        (scaled_kernel hK (t : ℂ)) m).trans (congrArg Prod.fst hm)
    have hd := iInf₂_le (f := fun (Γ : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N))
        (_ : ((PhysicalRemoval.model i F χ 1 C B S e).density Γ).1 = ρ) =>
          (PhysicalAttainmentFunctionals.mixedInternalEnergy F χ C B S e Γ : EReal)) _ hden
    have hle := hopt.trans_le (hzc.trans_le (hd.trans_eq
      (PhysicalAttainmentFunctionals.mixedModel_energy_coe i F χ C B S e _).symm))
    exact curve_zero heq hJ0 (EReal.coe_le_coe_iff.mp hle)
  have hb : 0 ≤ ‖K.val.2‖ ^ 2 + e ^ 2 / 2 * ∑' n, densityShift (PhysicalRemoval.potential N 1)
      (PhysicalRemovalKernels.full F χ N) f (s.vector n) :=
    add_nonneg (sq_nonneg _) (mul_nonneg (by positivity)
      (tsum_nonneg fun n => densityShift_nonneg _ _ f _))
  exact hA.tsum_eq.trans (linear_coefficient_zero hb hcurve)

include W BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **Coherent amplitudes vanish at zero current**: for an optimizer at `(ρ, 0)`
and every `f` with `√ω f, ω f ∈ L²`, `Tr(a(ω f) Γ) = 0` in every fermionic
spectral source. -/
theorem optimizer_zero_current_amplitude (he : 0 ≤ e) (hC₀ : 0 ≤ C₀)
    (m : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N)) {ρ : Density}
    (hm : (PhysicalRemoval.model i F χ 1 C B S e).density m = (ρ, 0))
    (hopt : ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
      PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e (ρ, 0))
    {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (s : PhysicalPFSource.SupportedSource N (PhysicalRemoval.potential N 1) B m.val.val) :
    sourceAmplitude (PhysicalRemoval.potential N 1) B s.toSource K = 0 := by
  have hre := optimizer_zero_current_re i F χ C B S e W BF BW core smooth C₀ scaled B₀ B₁ basis
    index Sob Rellich Hardy hLp hFM he hC₀ m hm hopt K hK s
  have him := optimizer_zero_current_re i F χ C B S e W BF BW core smooth C₀ scaled B₀ B₁ basis
    index Sob Rellich Hardy hLp hFM he hC₀ m hm hopt (Complex.I • K) (scaled_kernel hK Complex.I) s
  have hs : Summable (fun n => ⟪inclusion (Fin N × Fin 3) (PhysicalRemoval.potential N 1)
      (s.vector n), annihilationRef (PhysicalRemoval.potential N 1) K (s.vector n)⟫_ℂ) :=
    ((amplitude_summable (PhysicalRemoval.potential N 1) C (PhysicalRemovalKernels.full F χ N)
      (PhysicalRemovalKernels.full_measurable F χ N) (PhysicalRemovalKernels.bound F χ)
      (PhysicalRemovalKernels.full_bound F χ N) B S e s.toSource m.val.property.2.2 K).map
        (starRingEnd ℂ) Complex.continuous_conj).congr fun n => inner_conj_symm _ _
  apply Complex.ext
  · refine (Complex.hasSum_re hs.hasSum).tsum_eq.symm.trans ?_
    refine (tsum_congr fun n => re_inner_comm _ _).trans ?_
    exact hre.trans Complex.zero_re.symm
  · refine (Complex.hasSum_im hs.hasSum).tsum_eq.symm.trans ?_
    refine (tsum_congr fun n => amplitude_I (PhysicalRemoval.potential N 1) K (s.vector n)).trans ?_
    exact him.trans Complex.zero_im.symm

end Physical

end GptLean.PhysicalWeyl
