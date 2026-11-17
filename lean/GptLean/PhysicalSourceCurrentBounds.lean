import GptLean.NormWeakH1
import GptLean.PhysicalSourcePair

/-!
A priori bounds for the density-current pair of any electronic H1 wave
function with Hilbert-valued spectator fibers. The selected-particle source
is an H1 field with values in the spectator Hilbert space, so the norm chain
rule gives the weak gradient of the square root of the density. For a
covariant derivative `-i ∂ - e a` whose field part has a real fiber
expectation, the density gradient and the current are the imaginary and
real parts of one fiber scalar product, and Cauchy-Schwarz bounds both.
-/

noncomputable section

namespace GptLean.PhysicalSourceCurrentBounds

open MeasureTheory Filter PhysicalPairSpace PhysicalSourcePair PhysicalSourceMarginal
  PhysicalSourceCoordinates ElectronicH1Space SymmetricLift
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

section Pointwise

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_re_inner_div_norm_le (f d : H) : ‖(⟪f, d⟫_ℂ).re / ‖f‖‖ ≤ ‖d‖ := by
  by_cases hf : f = 0
  · subst hf
    simp
  have hp : 0 < ‖f‖ := norm_pos_iff.mpr hf
  rw [norm_div, norm_norm, Real.norm_eq_abs, div_le_iff₀ hp, mul_comm]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm f d)

/-- The density gradient and the combined current are the imaginary and
real parts of the same scalar product with the covariant derivative. -/
theorem inner_joint (f d a : H) (e : ℝ) (ha : (⟪f, a⟫_ℂ).im = 0) :
    (⟪f, d⟫_ℂ).re ^ 2 + (⟪f, (-Complex.I) • d - (e : ℂ) • a⟫_ℂ).re ^ 2 ≤
      ‖f‖ ^ 2 * ‖(-Complex.I) • d - (e : ℂ) • a‖ ^ 2 := by
  have him : (⟪f, (-Complex.I) • d - (e : ℂ) • a⟫_ℂ).im = -(⟪f, d⟫_ℂ).re := by
    rw [inner_sub_right, inner_smul_right, inner_smul_right, Complex.sub_im, Complex.mul_im,
      Complex.mul_im]
    simp [ha]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) f ((-Complex.I) • d - (e : ℂ) • a)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hcs 2
  have hz : ‖⟪f, (-Complex.I) • d - (e : ℂ) • a⟫_ℂ‖ ^ 2 =
      (⟪f, (-Complex.I) • d - (e : ℂ) • a⟫_ℂ).re ^ 2 +
        (⟪f, (-Complex.I) • d - (e : ℂ) • a⟫_ℂ).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [him, mul_pow] at *
  nlinarith [hz, hsq]

private theorem scalar_joint {N r x y K : ℝ} (hN : 0 ≤ N) (hr : 0 ≤ r) (hK : 0 ≤ K)
    (h : x ^ 2 + y ^ 2 ≤ r ^ 2 * K) :
    (Real.sqrt N * (x / r)) ^ 2 + (N * y) ^ 2 / (N * r ^ 2) ≤ N * K := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    have hz : (Real.sqrt N * (x / 0)) ^ 2 + (N * y) ^ 2 / (N * 0 ^ 2) = 0 := by simp
    rw [hz]
    exact mul_nonneg hN hK
  rcases hN.eq_or_lt with hN0 | hNpos
  · subst hN0
    have hz : (Real.sqrt 0 * (x / r)) ^ 2 + (0 * y) ^ 2 / (0 * r ^ 2) = 0 := by simp
    rw [hz, zero_mul]
  have hN' : N ≠ 0 := hNpos.ne'
  have hr' : r ≠ 0 := hpos.ne'
  rw [mul_pow, Real.sq_sqrt hN]
  have he : N * (x / r) ^ 2 + (N * y) ^ 2 / (N * r ^ 2) = N * ((x ^ 2 + y ^ 2) / r ^ 2) := by
    field_simp
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hN
  rw [div_le_iff₀ (pow_pos hpos 2), mul_comm]
  exact h

private theorem scalar_current {N r y K : ℝ} (hN : 0 ≤ N) (hr : 0 ≤ r) (hK : 0 ≤ K)
    (h : y ^ 2 ≤ r ^ 2 * K) : (N * y) ^ 2 / (N * r ^ 2) ≤ N * K := by
  have h' := scalar_joint (x := 0) (y := y) hN hr hK
    (by rw [zero_pow two_ne_zero, zero_add]; exact h)
  rwa [zero_div, mul_zero, zero_pow two_ne_zero, zero_add] at h'

/-- Pointwise joint bound at one position, with the density and the
current written through one fiber vector. -/
theorem joint_pointwise (N : ℕ) (e : ℝ) (f : H) (dd a D : Fin 3 → H) (g : Fin 3 → ℝ)
    (ρ : ℝ) (j : EuclideanSpace ℝ (Fin 3))
    (ha : ∀ b, (⟪f, a b⟫_ℂ).im = 0) (hD : ∀ b, D b = (-Complex.I) • dd b - (e : ℂ) • a b)
    (hg : ∀ b, g b = Real.sqrt N * ((⟪f, dd b⟫_ℂ).re / ‖f‖)) (hρ : ρ = N * ‖f‖ ^ 2)
    (hj : ∀ b, j b = N * (⟪f, D b⟫_ℂ).re) :
    ∑ b, g b ^ 2 + ‖j‖ ^ 2 / ρ ≤ N * ∑ b, ‖D b‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_div, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  rw [hg b, hj b, hρ]
  have h := inner_joint f (dd b) (a b) e (ha b)
  rw [← hD b] at h
  exact scalar_joint (Nat.cast_nonneg N) (norm_nonneg f) (sq_nonneg _) h

/-- Pointwise Cauchy-Schwarz bound for any current written through one fiber vector. -/
theorem current_pointwise (N : ℕ) (f : H) (d : Fin 3 → H) (ρ : ℝ)
    (j : EuclideanSpace ℝ (Fin 3)) (hρ : ρ = N * ‖f‖ ^ 2)
    (hj : ∀ b, j b = N * (⟪f, d b⟫_ℂ).re) :
    ‖j‖ ^ 2 / ρ ≤ N * ∑ b, ‖d b‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  rw [hj b, hρ]
  have hcs : (⟪f, d b⟫_ℂ).re ^ 2 ≤ ‖f‖ ^ 2 * ‖d b‖ ^ 2 := by
    have h1 := (Complex.abs_re_le_norm (⟪f, d b⟫_ℂ)).trans (norm_inner_le_norm f (d b))
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs, mul_pow] at h2
  exact scalar_current (Nat.cast_nonneg N) (norm_nonneg f) (sq_nonneg _) hcs

theorem current_add_component (N : ℝ) (f a a₁ a₂ : H) (h : a = a₁ + a₂) :
    N * (⟪f, a⟫_ℂ).re = N * (⟪f, a₁⟫_ℂ).re + N * (⟪f, a₂⟫_ℂ).re := by
  rw [h, inner_add_right, Complex.add_re, mul_add]

theorem sqrt_density_eq (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt ((N : ℝ) * r ^ 2) = Real.sqrt N * r := by
  rw [Real.sqrt_mul (Nat.cast_nonneg N), Real.sqrt_sq hr]

end Pointwise

private theorem l2_norm_sq {X K : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (u : Lp K 2 μ) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hn := Repair.toL2_norm_sq (Lp.memLp u)
  simp only [Lp.toLp_coeFn] at hn
  exact hn

section Wave

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- The weak gradient of the square root of the density, `N Re⟨Ψ, ∂Ψ⟩ₓ / √ρ`. -/
def sqrtDensityGradient (i : Fin N) (w : H1 H (Fin N × Fin 3)) (b : Fin 3)
    (x : PhysicalPairSpace.Position) : ℝ :=
  Real.sqrt N * ((⟪particleMap i (value w) x, particleMap i (derivative (i, b) w) x⟫_ℂ).re /
    ‖particleMap i (value w) x‖)

/-- The integrand of the joint density-current bound, with the quotient
equal to zero where the density vanishes. -/
def jointIntegrand (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) (x : PhysicalPairSpace.Position) : ℝ :=
  ∑ b, sqrtDensityGradient i w b x ^ 2 +
    ‖currentL1 (ofWaveFunction i w d) x‖ ^ 2 / densityL1 (ofWaveFunction i w d) x

theorem density_ae (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) :
    ∀ᵐ x ∂volume, densityL1 (ofWaveFunction i w d) x =
      (N : ℝ) * ‖particleMap i (value w) x‖ ^ 2 :=
  PhysicalPairRealization.density_ofSource_ae N (particleMap i (value w))
    (fun a => particleMap i (d a)) (Lp.memLp _) (particleSource_memLp_six i w)
    (fun _ => Lp.memLp _)

theorem current_ae (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) :
    ∀ᵐ x ∂volume, ∀ b, currentL1 (ofWaveFunction i w d) x b =
      (N : ℝ) * (⟪particleMap i (value w) x, particleMap i (d b) x⟫_ℂ).re := by
  filter_upwards [PhysicalPairRealization.current_ofSource_ae N (particleMap i (value w))
    (fun a => particleMap i (d a)) (Lp.memLp _) (particleSource_memLp_six i w)
    (fun _ => Lp.memLp _)] with x hx b
  exact congrArg (fun v : PhysicalPairSpace.Vector => v b) hx

theorem density_nonneg (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) :
    ∀ᵐ x ∂volume, 0 ≤ densityL1 (ofWaveFunction i w d) x := by
  filter_upwards [density_ae i w d] with x hx
  exact hx ▸ mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _)

theorem density_mass (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) (hw : ‖value w‖ = 1) :
    (∫ x, densityL1 (ofWaveFunction i w d) x) = N :=
  (integral_density_ofWaveFunction i w d).trans (by rw [hw, one_pow, mul_one])

theorem sqrtDensity_ae (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) :
    (fun x => Real.sqrt (densityL1 (ofWaveFunction i w d) x)) =ᵐ[volume]
      fun x => Real.sqrt N * ‖particleMap i (value w) x‖ := by
  filter_upwards [density_ae i w d] with x hx
  exact (congrArg Real.sqrt hx).trans (sqrt_density_eq N (norm_nonneg _))

theorem sqrtDensity_memLp (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) :
    MemLp (fun x => Real.sqrt (densityL1 (ofWaveFunction i w d) x)) 2 volume :=
  ((Lp.memLp (particleMap i (value w))).norm.const_mul (Real.sqrt N)).ae_eq
    (sqrtDensity_ae i w d).symm

theorem sqrtDensityGradient_aestronglyMeasurable (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (b : Fin 3) : AEStronglyMeasurable (sqrtDensityGradient i w b) volume := by
  have hf := Lp.aestronglyMeasurable (particleMap i (value w))
  have hd := Lp.aestronglyMeasurable (particleMap i (derivative (i, b) w))
  have hre : AEMeasurable (fun x => (⟪particleMap i (value w) x,
      particleMap i (derivative (i, b) w) x⟫_ℂ).re) volume :=
    Complex.continuous_re.measurable.comp_aemeasurable (hf.inner (𝕜 := ℂ) hd).aemeasurable
  exact ((hre.div hf.norm.aemeasurable).const_mul (Real.sqrt N)).aestronglyMeasurable

theorem norm_sqrtDensityGradient_le (i : Fin N) (w : H1 H (Fin N × Fin 3)) (b : Fin 3)
    (x : PhysicalPairSpace.Position) :
    ‖sqrtDensityGradient i w b x‖ ≤ Real.sqrt N * ‖particleMap i (derivative (i, b) w) x‖ := by
  unfold sqrtDensityGradient
  rw [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (norm_re_inner_div_norm_le _ _) (Real.sqrt_nonneg _)

theorem sqrtDensityGradient_memLp (i : Fin N) (w : H1 H (Fin N × Fin 3)) (b : Fin 3) :
    MemLp (sqrtDensityGradient i w b) 2 volume :=
  ((Lp.memLp (particleMap i (derivative (i, b) w))).norm.const_mul (Real.sqrt N)).mono'
    (sqrtDensityGradient_aestronglyMeasurable i w b)
    (ae_of_all _ fun x => norm_sqrtDensityGradient_le i w b x)

/-- `√ρ` is weakly differentiable, with the explicit gradient. -/
theorem sqrtDensity_weak (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) :
    HasWeakH1Local (fun x => Real.sqrt (densityL1 (ofWaveFunction i w d) x))
      (sqrtDensityGradient i w) := by
  let := InnerProductSpace.rclikeToReal ℂ (Lp H 2 (volume : Measure (Spectator i)))
  have hsrc : HasWeakH1Local (fun x => particleMap i (value w) x)
      (fun b x => particleMap i (derivative (i, b) w) x) :=
    ElectronicH1Space.weak (particleSource i w)
  have hs := Repair.weakH1Local_map (Real.sqrt N • ContinuousLinearMap.id ℝ ℝ)
    (NormWeakH1.norm_weakH1Local hsrc)
  exact hs.congr (sqrtDensity_ae i w d).symm (fun b => ae_of_all _ fun x => rfl)

omit [CompleteSpace H] in
/-- Pointwise bounds by squared fiber norms integrate to squared L2 norms. -/
theorem integral_le_of_fiber_bound (i : Fin N) {F : PhysicalPairSpace.Position → ℝ}
    (d : Fin 3 → L2 H (Fin N × Fin 3)) (c : ℝ)
    (hF : AEStronglyMeasurable F volume) (h0 : ∀ᵐ x ∂volume, 0 ≤ F x)
    (hle : ∀ᵐ x ∂volume, F x ≤ c * ∑ b, ‖particleMap i (d b) x‖ ^ 2) :
    Integrable F volume ∧ (∫ x, F x) ≤ c * ∑ b, ‖d b‖ ^ 2 := by
  have hi (b : Fin 3) : Integrable (fun x => ‖particleMap i (d b) x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hG : Integrable (fun x => c * ∑ b, ‖particleMap i (d b) x‖ ^ 2) volume :=
    (integrable_finsetSum _ fun b _ => hi b).const_mul c
  have hFi : Integrable F volume := hG.mono' hF (by
    filter_upwards [h0, hle] with x hx hy
    exact (Real.norm_of_nonneg hx).trans_le hy)
  refine ⟨hFi, ?_⟩
  calc
    (∫ x, F x) ≤ ∫ x, c * ∑ b, ‖particleMap i (d b) x‖ ^ 2 := integral_mono_ae hFi hG hle
    _ = c * ∑ b, ‖particleMap i (d b)‖ ^ 2 := by
      rw [integral_const_mul, integral_finsetSum _ fun b _ => hi b]
      exact congrArg (c * ·) (Finset.sum_congr rfl fun b _ => (l2_norm_sq _).symm)
    _ = c * ∑ b, ‖d b‖ ^ 2 :=
      congrArg (c * ·) (Finset.sum_congr rfl fun b _ =>
        congrArg (· ^ 2) ((particleMap i).norm_map (d b)))

/-- The fiber pointwise form of the covariant decomposition. -/
theorem particleMap_covariant_ae (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (a d : Fin 3 → L2 H (Fin N × Fin 3)) (e : ℝ)
    (hd : ∀ b, d b = (-Complex.I) • derivative (i, b) w - (e : ℂ) • a b) :
    ∀ᵐ x ∂volume, ∀ b, particleMap i (d b) x =
      (-Complex.I) • particleMap i (derivative (i, b) w) x - (e : ℂ) • particleMap i (a b) x := by
  rw [ae_all_iff]
  intro b
  have hm : particleMap i (d b) = (-Complex.I) • particleMap i (derivative (i, b) w) -
      (e : ℂ) • particleMap i (a b) :=
    (congrArg (particleMap i) (hd b)).trans ((map_sub _ _ _).trans
      (congrArg₂ (· - ·) (map_smul _ _ _) (map_smul _ _ _)))
  filter_upwards [Lp.coeFn_sub ((-Complex.I) • particleMap i (derivative (i, b) w))
      ((e : ℂ) • particleMap i (a b)),
    Lp.coeFn_smul (-Complex.I) (particleMap i (derivative (i, b) w)),
    Lp.coeFn_smul (e : ℂ) (particleMap i (a b))] with x h₁ h₂ h₃
  exact (congrFun (congrArg (fun F : L2 (Lp H 2 (volume : Measure (Spectator i))) (Fin 3) =>
    (F : PhysicalPairSpace.Position → Lp H 2 (volume : Measure (Spectator i)))) hm) x).trans
      (h₁.trans (congrArg₂ (· - ·) h₂ h₃))

/-- Joint bound for any covariant derivative `-i ∂ - e a` whose field part
has a real fiber expectation. -/
theorem joint_bound (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (a d : Fin 3 → L2 H (Fin N × Fin 3)) (e : ℝ)
    (ha : ∀ b, ∀ᵐ x ∂volume,
      (⟪particleMap i (value w) x, particleMap i (a b) x⟫_ℂ).im = 0)
    (hd : ∀ b, d b = (-Complex.I) • derivative (i, b) w - (e : ℂ) • a b) :
    Integrable (jointIntegrand i w d) volume ∧
      (∫ x, jointIntegrand i w d x) ≤ N * ∑ b, ‖d b‖ ^ 2 := by
  apply integral_le_of_fiber_bound i d N
  · have hj := (Lp.aestronglyMeasurable (currentL1 (ofWaveFunction i w d))).norm.pow 2
    have hρ := Lp.aestronglyMeasurable (densityL1 (ofWaveFunction i w d))
    have hs := Finset.aestronglyMeasurable_sum Finset.univ fun b _ =>
      (sqrtDensityGradient_aestronglyMeasurable i w b).pow 2
    refine (hs.add (hj.aemeasurable.div hρ.aemeasurable).aestronglyMeasurable).congr
      (ae_of_all _ fun x => ?_)
    simp only [jointIntegrand, Pi.add_apply, Finset.sum_apply, Pi.pow_apply, Pi.div_apply]
  · filter_upwards [density_nonneg i w d] with x hx
    exact add_nonneg (Finset.sum_nonneg fun b _ => sq_nonneg _)
      (div_nonneg (sq_nonneg _) hx)
  · filter_upwards [density_ae i w d, current_ae i w d, particleMap_covariant_ae i w a d e hd,
      ae_all_iff.mpr ha] with x hρ hj hD ha'
    exact joint_pointwise N e (particleMap i (value w) x)
      (fun b => particleMap i (derivative (i, b) w) x) (fun b => particleMap i (a b) x)
      (fun b => particleMap i (d b) x) (fun b => sqrtDensityGradient i w b x) _ _
      ha' hD (fun b => rfl) hρ hj

/-- Cauchy-Schwarz bound for the current of any square-integrable derivative
family. The density may be taken from any pair of the same wave function. -/
theorem current_bound (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (d₀ d : Fin 3 → L2 H (Fin N × Fin 3)) :
    Integrable (fun x => ‖currentL1 (ofWaveFunction i w d) x‖ ^ 2 /
        densityL1 (ofWaveFunction i w d₀) x) volume ∧
      (∫ x, ‖currentL1 (ofWaveFunction i w d) x‖ ^ 2 / densityL1 (ofWaveFunction i w d₀) x) ≤
        N * ∑ b, ‖d b‖ ^ 2 := by
  apply integral_le_of_fiber_bound i d N
  · have hj := (Lp.aestronglyMeasurable (currentL1 (ofWaveFunction i w d))).norm.pow 2
    have hρ := Lp.aestronglyMeasurable (densityL1 (ofWaveFunction i w d₀))
    exact (hj.aemeasurable.div hρ.aemeasurable).aestronglyMeasurable
  · filter_upwards [density_nonneg i w d₀] with x hx
    exact div_nonneg (sq_nonneg _) hx
  · filter_upwards [density_ae i w d₀, current_ae i w d] with x hρ hj
    exact current_pointwise N (particleMap i (value w) x) (fun b => particleMap i (d b) x)
      _ _ hρ hj

/-- Every pair of the same wave function has the same density. -/
theorem densityL1_eq (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (d₀ d : Fin 3 → L2 H (Fin N × Fin 3)) :
    densityL1 (ofWaveFunction i w d) = densityL1 (ofWaveFunction i w d₀) := by
  apply Lp.ext
  filter_upwards [density_ae i w d, density_ae i w d₀] with x h h₀
  exact h.trans h₀.symm

/-- The current is additive in the derivative family. -/
theorem currentL1_add (i : Fin N) (w : H1 H (Fin N × Fin 3))
    (d d₁ d₂ : Fin 3 → L2 H (Fin N × Fin 3)) (hd : ∀ b, d b = d₁ b + d₂ b) :
    currentL1 (ofWaveFunction i w d) =
      currentL1 (ofWaveFunction i w d₁) + currentL1 (ofWaveFunction i w d₂) := by
  have hsum : ∀ᵐ x ∂volume, ∀ b, particleMap i (d b) x =
      particleMap i (d₁ b) x + particleMap i (d₂ b) x := by
    rw [ae_all_iff]
    intro b
    have hm : particleMap i (d b) = particleMap i (d₁ b) + particleMap i (d₂ b) :=
      (congrArg (particleMap i) (hd b)).trans (map_add _ _ _)
    filter_upwards [Lp.coeFn_add (particleMap i (d₁ b)) (particleMap i (d₂ b))] with x hx
    exact (congrFun (congrArg (fun F : L2 (Lp H 2 (volume : Measure (Spectator i))) (Fin 3) =>
      (F : PhysicalPairSpace.Position → Lp H 2 (volume : Measure (Spectator i)))) hm) x).trans hx
  apply Lp.ext
  filter_upwards [current_ae i w d, current_ae i w d₁, current_ae i w d₂, hsum,
    Lp.coeFn_add (currentL1 (ofWaveFunction i w d₁)) (currentL1 (ofWaveFunction i w d₂))]
    with x h h₁ h₂ hs ha
  refine (PiLp.ext fun b => ?_).trans ha.symm
  exact (h b).trans ((current_add_component _ _ _ _ _ (hs b)).trans
    (congrArg₂ (· + ·) (h₁ b) (h₂ b)).symm)

end Wave

end GptLean.PhysicalSourceCurrentBounds
