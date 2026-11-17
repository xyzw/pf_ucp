import GptLean.TransformationsGaugeH1
import GptLean.PhysicalPairTests
import GptLean.PhysicalElectronicFermions
import GptLean.SymmetricLift.PairEnergyIntegrability

/-!
Spatial gauge functions and their action on the physical density-current pair.

A spatial gauge function `g` on `ℝ³` is differentiable with bounded first
derivatives. Its configuration-space gauge function is `G(X) = ∑ⱼ g(xⱼ)`,
whose derivative in the coordinate `(j, a)` is `∂ₐ g(xⱼ)`. It is invariant
under particle permutations, so its phase preserves the fermionic subspace.

On the article's pair space `X × Y` the gauge acts by
`(ρ, j) ↦ (ρ, j + ρ ∇g)`. The current shift lies in `L¹ ∩ L^{3/2}` because
`ρ ∈ L¹ ∩ L³` interpolates into `L^{3/2}` and `∇g` is bounded. The map is a
bijection with inverse given by `-g`. The energy shift of `F-gauge` is
`∫ ∇g · j + ½ ∫ ρ |∇g|²`.
-/

noncomputable section

namespace GptLean.TransformationsGauge

open MeasureTheory PhysicalPairSpace SymmetricLift TransformationsPhase
open scoped ENNReal

set_option maxHeartbeats 400000

section Interpolation

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E]

/-- Elementary interpolation: `L¹ ∩ L³ ⊆ L^{3/2}`. -/
theorem memLp_three_halves {f : X → E} (h1 : MemLp f 1 μ) (h3 : MemLp f 3 μ) :
    MemLp f (3 / 2) μ := by
  have hf := h1.aestronglyMeasurable
  refine (integrable_norm_rpow_iff hf (by norm_num) (by norm_num [ENNReal.div_eq_top])).mp ?_
  have hi1 : Integrable (fun x => ‖f x‖) μ := (memLp_one_iff_integrable.mp h1).norm
  have hi3 : Integrable (fun x => ‖f x‖ ^ (3 : ℝ≥0∞).toReal) μ :=
    h3.integrable_norm_rpow (by norm_num) (by norm_num)
  refine (hi1.add hi3).mono' ?_ ?_
  · exact (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    have h32 : (3 / 2 : ℝ≥0∞).toReal = 3 / 2 := by
      rw [ENNReal.toReal_div]
      norm_num
    have h3' : (3 : ℝ≥0∞).toReal = 3 := by norm_num
    rw [h32, h3', Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    change ‖f x‖ ^ (3 / 2 : ℝ) ≤ ‖f x‖ + ‖f x‖ ^ (3 : ℝ)
    rcases le_total ‖f x‖ 1 with ht | ht
    · have h := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (f x)) ht zero_le_one
        (show (1 : ℝ) ≤ 3 / 2 by norm_num)
      rw [Real.rpow_one] at h
      linarith [Real.rpow_nonneg (norm_nonneg (f x)) (3 : ℝ)]
    · have h := Real.rpow_le_rpow_of_exponent_le ht (show (3 / 2 : ℝ) ≤ 3 by norm_num)
      linarith [norm_nonneg (f x)]

end Interpolation

/-- A differentiable gauge function on physical space with bounded gradient. -/
structure SpatialGauge where
  fn : Position → ℝ
  differentiable : Differentiable ℝ fn
  derivativeBound : ℝ
  derivative_bounded : ∀ a y, |fderiv ℝ fn y (EuclideanSpace.single a 1)| ≤ derivativeBound

namespace SpatialGauge

variable (g : SpatialGauge)

/-- The component `∂ₐ g`. -/
def gradient (a : Fin 3) (y : Position) : ℝ := fderiv ℝ g.fn y (EuclideanSpace.single a 1)

theorem gradient_measurable (a : Fin 3) : Measurable (g.gradient a) :=
  measurable_fderiv_apply_const ℝ g.fn (EuclideanSpace.single a 1)

theorem abs_gradient_le (a : Fin 3) (y : Position) : |g.gradient a y| ≤ g.derivativeBound :=
  g.derivative_bounded a y

theorem derivativeBound_nonneg : 0 ≤ g.derivativeBound :=
  (abs_nonneg _).trans (g.derivative_bounded 0 0)

/-- The gauge function `-g`. -/
def neg : SpatialGauge where
  fn y := -g.fn y
  differentiable := g.differentiable.neg
  derivativeBound := g.derivativeBound
  derivative_bounded a y := by
    rw [fderiv_fun_neg, ContinuousLinearMap.neg_apply, abs_neg]
    exact g.derivative_bounded a y

theorem neg_gradient (a : Fin 3) (y : Position) : g.neg.gradient a y = -g.gradient a y := by
  change fderiv ℝ (fun z => -g.fn z) y _ = _
  rw [fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  rfl

/-- The gradient `∇g` as a vector field. -/
def gradientVector (y : Position) : Vector := WithLp.toLp 2 (fun a => g.gradient a y)

theorem gradientVector_apply (y : Position) (a : Fin 3) :
    g.gradientVector y a = g.gradient a y := rfl

theorem gradientVector_measurable : Measurable g.gradientVector :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
    (measurable_pi_lambda _ fun a => g.gradient_measurable a)

/-- A uniform bound on the length of `∇g`. -/
def vectorBound : ℝ := Real.sqrt (3 * g.derivativeBound ^ 2)

theorem norm_gradientVector_le (y : Position) : ‖g.gradientVector y‖ ≤ g.vectorBound := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc (∑ a, ‖g.gradientVector y a‖ ^ 2) ≤ ∑ _a : Fin 3, g.derivativeBound ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        rw [gradientVector_apply, Real.norm_eq_abs, sq_abs]
        have h := g.abs_gradient_le a y
        nlinarith [abs_nonneg (g.gradient a y), sq_abs (g.gradient a y)]
    _ = 3 * g.derivativeBound ^ 2 := by simp

theorem neg_gradientVector (y : Position) : g.neg.gradientVector y = -g.gradientVector y := by
  ext a
  simp only [gradientVector_apply, neg_gradient, PiLp.neg_apply]

/-! ### The action on density-current pairs -/

theorem density_memLp_three (p : Pair) : MemLp (densityL1 p) 3 volume :=
  (Lp.memLp (densityL3 p)).ae_eq (coe_fst_eq_coe_snd p.1).symm

theorem current_memLp_three_halves (p : Pair) : MemLp (currentL1 p) (3 / 2) volume :=
  (Lp.memLp (currentL32 p)).ae_eq (coe_fst_eq_coe_snd p.2).symm

theorem shift_aestronglyMeasurable (p : Pair) :
    AEStronglyMeasurable (fun x => densityL1 p x • g.gradientVector x) volume :=
  (Lp.aestronglyMeasurable (densityL1 p)).smul g.gradientVector_measurable.aestronglyMeasurable

theorem shift_norm_le (p : Pair) (x : Position) :
    ‖densityL1 p x • g.gradientVector x‖ ≤ g.vectorBound * ‖densityL1 p x‖ := by
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (g.norm_gradientVector_le x) (norm_nonneg _)

theorem shift_memLp_one (p : Pair) :
    MemLp (fun x => densityL1 p x • g.gradientVector x) 1 volume :=
  (Lp.memLp (densityL1 p)).of_le_mul (g.shift_aestronglyMeasurable p)
    (ae_of_all _ (g.shift_norm_le p))

theorem shift_memLp_three_halves (p : Pair) :
    MemLp (fun x => densityL1 p x • g.gradientVector x) (3 / 2) volume :=
  (memLp_three_halves (Lp.memLp (densityL1 p)) (density_memLp_three p)).of_le_mul
    (g.shift_aestronglyMeasurable p) (ae_of_all _ (g.shift_norm_le p))

/-- The gauge action `(ρ, j) ↦ (ρ, j + ρ ∇g)` on the article pair space. -/
def shiftPair (p : Pair) : Pair :=
  ofFunctions (densityL1 p) (fun x => currentL1 p x + densityL1 p x • g.gradientVector x)
    (Lp.memLp _) (density_memLp_three p)
    ((Lp.memLp (currentL1 p)).add (g.shift_memLp_one p))
    ((current_memLp_three_halves p).add (g.shift_memLp_three_halves p))

theorem densityL1_shiftPair (p : Pair) : densityL1 (g.shiftPair p) = densityL1 p := by
  simp only [shiftPair, densityL1_ofFunctions, Lp.toLp_coeFn]

theorem currentL1_shiftPair (p : Pair) :
    (currentL1 (g.shiftPair p) : Position → Vector) =ᵐ[volume]
      fun x => currentL1 p x + densityL1 p x • g.gradientVector x :=
  ((Lp.memLp (currentL1 p)).add (g.shift_memLp_one p)).coeFn_toLp

/-- The negative gauge undoes the pair shift. -/
theorem neg_shiftPair (p : Pair) : g.neg.shiftPair (g.shiftPair p) = p := by
  apply pair_ext_ae
  · rw [g.neg.densityL1_shiftPair, g.densityL1_shiftPair]
  · filter_upwards [g.neg.currentL1_shiftPair (g.shiftPair p), g.currentL1_shiftPair p]
      with x h₁ h₂
    rw [g.densityL1_shiftPair] at h₁
    rw [h₁, h₂, neg_gradientVector, smul_neg]
    abel

theorem neg_neg_fn : g.neg.neg.fn = g.fn := by
  funext y
  exact neg_neg (g.fn y)

theorem shiftPair_neg (p : Pair) : g.shiftPair (g.neg.shiftPair p) = p := by
  apply pair_ext_ae
  · rw [g.densityL1_shiftPair, g.neg.densityL1_shiftPair]
  · filter_upwards [g.currentL1_shiftPair (g.neg.shiftPair p), g.neg.currentL1_shiftPair p]
      with x h₁ h₂
    rw [g.neg.densityL1_shiftPair] at h₁
    rw [h₁, h₂, neg_gradientVector, smul_neg]
    abel

/-- The gauge action on pairs as a bijection. -/
def shiftEquiv : Pair ≃ Pair where
  toFun := g.shiftPair
  invFun := g.neg.shiftPair
  left_inv := g.neg_shiftPair
  right_inv := g.shiftPair_neg

/-- The linear energy shift `∫ ∇g · j + ½ ∫ ρ |∇g|²` of `F-gauge`. -/
def energyShift (p : Pair) : ℝ :=
  (∑ a, ∫ x, g.gradient a x * currentL1 p x a) +
    (1 / 2 : ℝ) * ∫ x, (∑ a, g.gradient a x ^ 2) * densityL1 p x

theorem tested_density_shiftPair (p : Pair) (t : Position → ℝ) :
    (∫ x, t x * densityL1 (g.shiftPair p) x) = ∫ x, t x * densityL1 p x := by
  rw [g.densityL1_shiftPair]

theorem tested_current_shiftPair (p : Pair) (b : Fin 3) (t : Position → ℝ)
    (ht : AEStronglyMeasurable t volume) {c : ℝ} (hc : ∀ x, ‖t x‖ ≤ c) :
    (∫ x, t x * currentL1 (g.shiftPair p) x b) =
      (∫ x, t x * currentL1 p x b) + ∫ x, (t x * g.gradient b x) * densityL1 p x := by
  have hj := current_component_integrable p b
  have hρ := density_integrable p
  have h₁ : Integrable (fun x => t x * currentL1 p x b) volume :=
    hj.bdd_mul ht (ae_of_all _ hc)
  have hgb : AEStronglyMeasurable (fun x => t x * g.gradient b x) volume :=
    ht.mul (g.gradient_measurable b).aestronglyMeasurable
  have h₂ : Integrable (fun x => (t x * g.gradient b x) * densityL1 p x) volume :=
    hρ.bdd_mul hgb (c := c * g.derivativeBound) (ae_of_all _ fun x => by
      rw [norm_mul]
      exact mul_le_mul (hc x) (by rw [Real.norm_eq_abs]; exact g.abs_gradient_le b x)
        (norm_nonneg _) ((norm_nonneg _).trans (hc x)))
  rw [← integral_add h₁ h₂]
  apply integral_congr_ae
  filter_upwards [g.currentL1_shiftPair p] with x hx
  rw [hx, PiLp.add_apply, PiLp.smul_apply, gradientVector_apply, smul_eq_mul]
  ring

/-! ### The configuration-space gauge `G(X) = ∑ⱼ g(xⱼ)` -/

variable {N : ℕ}

/-- The particle projection as a continuous linear map. -/
def particleCLM (j : Fin N) : Configuration N →L[ℝ] Position :=
  LinearMap.toContinuousLinearMap (particleLinear j)

theorem particleCLM_apply (j : Fin N) (z : Configuration N) :
    particleCLM j z = particle z j := rfl

theorem particle_single (q : Fin N × Fin 3) (j : Fin N) :
    particle (EuclideanSpace.single q (1 : ℝ)) j =
      if j = q.1 then EuclideanSpace.single q.2 1 else 0 := by
  ext a
  by_cases hj : j = q.1
  · subst hj
    simp only [particle, if_true, EuclideanSpace.single_apply, Prod.ext_iff, true_and]
  · simp only [particle, if_neg hj, EuclideanSpace.single_apply, Prod.ext_iff, hj, false_and,
      if_false]
    rfl

theorem particle_permute (π : Equiv.Perm (Fin N)) (z : Configuration N) (j : Fin N) :
    particle (permuteConfiguration π z) j = particle z (π.symm j) := by
  ext a
  rfl

theorem hasFDerivAt_configuration (z : Configuration N) :
    HasFDerivAt (fun z : Configuration N => ∑ j, g.fn (particle z j))
      (∑ j, (fderiv ℝ g.fn (particle z j)).comp (particleCLM j)) z := by
  apply HasFDerivAt.fun_sum
  intro j _
  exact (g.differentiable (particle z j)).hasFDerivAt.comp z (particleCLM j).hasFDerivAt

theorem configuration_fderiv_single (z : Configuration N) (q : Fin N × Fin 3) :
    fderiv ℝ (fun z : Configuration N => ∑ j, g.fn (particle z j)) z
      (EuclideanSpace.single q 1) = g.gradient q.2 (particle z q.1) := by
  rw [(g.hasFDerivAt_configuration z).fderiv, ContinuousLinearMap.sum_apply]
  rw [Finset.sum_eq_single q.1]
  · rw [ContinuousLinearMap.comp_apply, particleCLM_apply, particle_single, if_pos rfl]
    rfl
  · intro j _ hj
    rw [ContinuousLinearMap.comp_apply, particleCLM_apply, particle_single, if_neg hj, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The configuration-space gauge function `G(X) = ∑ⱼ g(xⱼ)`. -/
def configuration (N : ℕ) : GaugeFunction (Fin N × Fin 3) where
  fn z := ∑ j, g.fn (particle z j)
  differentiable z := (g.hasFDerivAt_configuration z).differentiableAt
  derivativeBound := g.derivativeBound
  derivative_bounded q z := by
    rw [g.configuration_fderiv_single z q]
    exact g.abs_gradient_le q.2 (particle z q.1)

theorem configuration_gradient (q : Fin N × Fin 3) (z : Configuration N) :
    (g.configuration N).gradient q z = g.gradient q.2 (particle z q.1) :=
  g.configuration_fderiv_single z q

theorem configuration_permute (π : Equiv.Perm (Fin N)) (z : Configuration N) :
    (g.configuration N).fn (permuteConfiguration π z) = (g.configuration N).fn z := by
  change ∑ j, g.fn (particle (permuteConfiguration π z) j) = ∑ j, g.fn (particle z j)
  simp_rw [particle_permute]
  exact Equiv.sum_comp π.symm (fun j => g.fn (particle z j))

theorem configuration_neg_fn : (g.neg.configuration N).fn = (g.configuration N).neg.fn := by
  funext z
  change ∑ j, -g.fn (particle z j) = -∑ j, g.fn (particle z j)
  rw [Finset.sum_neg_distrib]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The configuration phase commutes with every particle permutation. -/
theorem permutation_phaseL2 (π : Equiv.Perm (Fin N))
    (v : PhysicalElectronicFermions.FullSpace N H) :
    PhysicalElectronicFermions.permutation N H π ((g.configuration N).phaseL2 v) =
      (g.configuration N).phaseL2 (PhysicalElectronicFermions.permutation N H π v) := by
  apply Lp.ext
  have hcomp := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae_eq_comp
    ((g.configuration N).phaseL2_ae v)
  filter_upwards [PhysicalElectronicFermions.permutation_ae N H π ((g.configuration N).phaseL2 v),
    hcomp, (g.configuration N).phaseL2_ae (PhysicalElectronicFermions.permutation N H π v),
    PhysicalElectronicFermions.permutation_ae N H π v] with x h₁ h₂ h₃ h₄
  rw [h₁, h₃, h₄]
  simp only [Function.comp_apply] at h₂
  rw [h₂]
  unfold factor
  rw [g.configuration_permute π x]

theorem phaseL2_mem_fermionic {v : PhysicalElectronicFermions.FullSpace N H}
    (hv : v ∈ PhysicalElectronicFermions.fermionicSubspace N H) :
    (g.configuration N).phaseL2 v ∈ PhysicalElectronicFermions.fermionicSubspace N H := by
  intro π
  rw [g.permutation_phaseL2 π v, hv π, map_smul]

end SpatialGauge

end GptLean.TransformationsGauge
