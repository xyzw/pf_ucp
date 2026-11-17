import GptLean.TransformationsPhase
import GptLean.ElectronicH1DifferentiableMultiplier
import GptLean.ElectronicH1Complex

/-!
The gauge phase on the actual complex electronic H1 graph.

A gauge function `G` on configuration space is differentiable with bounded
first derivatives. Multiplication by `exp (i G)` preserves the weak H1 graph,
and its weak derivatives obey the product rule
`∂ᵢ (exp (i G) u) = exp (i G) (∂ᵢ u + i (∂ᵢ G) u)`.
The proof writes the phase as `cos G + i sin G` and applies the proved
real differentiable-multiplier theorem to both parts. The inverse map is the
phase of `-G`. This is the electronic part of `prop-gauge-covariance` for
gauge functions with bounded gradient.
-/

noncomputable section

namespace GptLean.TransformationsGauge

open MeasureTheory ElectronicH1Space ElectronicH1Multiplier TransformationsPhase
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable (I : Type*) [Fintype I] [DecidableEq I]

/-- A differentiable gauge function on configuration space with bounded
first derivatives. -/
structure GaugeFunction where
  fn : EuclideanSpace ℝ I → ℝ
  differentiable : Differentiable ℝ fn
  derivativeBound : ℝ
  derivative_bounded : ∀ i x, |fderiv ℝ fn x (EuclideanSpace.single i 1)| ≤ derivativeBound

namespace GaugeFunction

variable {I} (G : GaugeFunction I)

/-- The coordinate derivative `∂ᵢ G`. -/
def gradient (i : I) (x : EuclideanSpace ℝ I) : ℝ :=
  fderiv ℝ G.fn x (EuclideanSpace.single i 1)

theorem gradient_measurable (i : I) : Measurable (G.gradient i) :=
  measurable_fderiv_apply_const ℝ G.fn (EuclideanSpace.single i 1)

theorem aestronglyMeasurable : AEStronglyMeasurable G.fn volume :=
  G.differentiable.continuous.aestronglyMeasurable

theorem gradient_bounded (i : I) (x : EuclideanSpace ℝ I) :
    |G.gradient i x| ≤ G.derivativeBound := G.derivative_bounded i x

/-- The gauge function `-G`, which gives the inverse phase. -/
def neg : GaugeFunction I where
  fn x := -G.fn x
  differentiable := G.differentiable.neg
  derivativeBound := G.derivativeBound
  derivative_bounded i x := by
    rw [fderiv_fun_neg, ContinuousLinearMap.neg_apply, abs_neg]
    exact G.derivative_bounded i x

theorem neg_gradient (i : I) (x : EuclideanSpace ℝ I) :
    G.neg.gradient i x = -G.gradient i x := by
  change fderiv ℝ (fun y => -G.fn y) x _ = _
  rw [fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  rfl

theorem hasFDerivAt_cos (x : EuclideanSpace ℝ I) :
    HasFDerivAt (fun y => Real.cos (G.fn y)) (-Real.sin (G.fn x) • fderiv ℝ G.fn x) x :=
  (G.differentiable x).hasFDerivAt.cos

theorem hasFDerivAt_sin (x : EuclideanSpace ℝ I) :
    HasFDerivAt (fun y => Real.sin (G.fn y)) (Real.cos (G.fn x) • fderiv ℝ G.fn x) x :=
  (G.differentiable x).hasFDerivAt.sin

private theorem scaled_bound {c d D : ℝ} (hc : |c| ≤ 1) (hd : |d| ≤ D) : |c * d| ≤ D := by
  rw [abs_mul]
  calc |c| * |d| ≤ 1 * D :=
        mul_le_mul hc hd (abs_nonneg _) zero_le_one
    _ = D := one_mul D

/-- The real part `cos G` as a bounded differentiable multiplier. -/
def cosMultiplier : DifferentiableMultiplier I where
  weight x := Real.cos (G.fn x)
  differentiable x := (G.hasFDerivAt_cos x).differentiableAt
  bound := 1
  bounded x := Real.abs_cos_le_one _
  derivativeBound := G.derivativeBound
  derivative_bounded i x := by
    rw [(G.hasFDerivAt_cos x).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact scaled_bound (by rw [abs_neg]; exact Real.abs_sin_le_one _) (G.derivative_bounded i x)

/-- The imaginary part `sin G` as a bounded differentiable multiplier. -/
def sinMultiplier : DifferentiableMultiplier I where
  weight x := Real.sin (G.fn x)
  differentiable x := (G.hasFDerivAt_sin x).differentiableAt
  bound := 1
  bounded x := Real.abs_sin_le_one _
  derivativeBound := G.derivativeBound
  derivative_bounded i x := by
    rw [(G.hasFDerivAt_sin x).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact scaled_bound (Real.abs_cos_le_one _) (G.derivative_bounded i x)

theorem cosMultiplier_gradient (i : I) (x : EuclideanSpace ℝ I) :
    G.cosMultiplier.gradient i x = -Real.sin (G.fn x) * G.gradient i x := by
  change fderiv ℝ (fun y => Real.cos (G.fn y)) x _ = _
  rw [(G.hasFDerivAt_cos x).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

theorem sinMultiplier_gradient (i : I) (x : EuclideanSpace ℝ I) :
    G.sinMultiplier.gradient i x = Real.cos (G.fn x) * G.gradient i x := by
  change fderiv ℝ (fun y => Real.sin (G.fn y)) x _ = _
  rw [(G.hasFDerivAt_sin x).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The phase `exp (i G)` on electronic L². -/
def phaseL2 : L2 H I ≃ₗᵢ[ℂ] L2 H I := phase G.aestronglyMeasurable

/-- Multiplication by the real coordinate derivative `∂ᵢ G`. -/
def gradientMultiplier (i : I) : L2 H I →L[ℂ] L2 H I :=
  PhotonLocalization.realL2Multiplier (G.gradient i)
    (G.gradient_measurable i).aestronglyMeasurable G.derivativeBound
    (ae_of_all _ (G.gradient_bounded i))

theorem phaseL2_ae (u : L2 H I) :
    G.phaseL2 u =ᵐ[volume] fun x => factor G.fn x • u x :=
  phase_ae G.aestronglyMeasurable u

theorem gradientMultiplier_ae (i : I) (u : L2 H I) :
    G.gradientMultiplier i u =ᵐ[volume] fun x => G.gradient i x • u x :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ u

theorem gradientMultiplier_norm_le (i : I) (u : L2 H I) :
    ‖G.gradientMultiplier i u‖ ≤ G.derivativeBound * ‖u‖ :=
  PhotonLocalization.realL2Multiplier_norm_le _ _ _ _ u

/-- The phase commutes with multiplication by `∂ᵢ G`. -/
theorem gradientMultiplier_phaseL2 (i : I) (u : L2 H I) :
    G.gradientMultiplier i (G.phaseL2 u) = G.phaseL2 (G.gradientMultiplier i u) := by
  apply Lp.ext
  filter_upwards [G.gradientMultiplier_ae i (G.phaseL2 u), G.phaseL2_ae u,
    G.phaseL2_ae (G.gradientMultiplier i u), G.gradientMultiplier_ae i u]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, smul_comm]

private theorem factor_smul (t : ℝ) (v : H) :
    Complex.exp ((t : ℂ) * Complex.I) • v =
      Real.cos t • v + Complex.I • (Real.sin t • v) := by
  rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.exp_mul_I]
  congr 1
  push_cast
  ring

private theorem factor_derivative_smul (t g : ℝ) (a b : H) :
    Complex.exp ((t : ℂ) * Complex.I) • (a + Complex.I • (g • b)) =
      (Real.cos t • a + (-Real.sin t * g) • b) +
        Complex.I • (Real.sin t • a + (Real.cos t * g) • b) := by
  have e1 : Complex.exp ((t : ℂ) * Complex.I) =
      ((Real.cos t : ℝ) : ℂ) + Complex.I * ((Real.sin t : ℝ) : ℂ) := by
    rw [Complex.exp_mul_I]
    push_cast
    ring
  have e2 : Complex.exp ((t : ℂ) * Complex.I) * (Complex.I * (g : ℂ)) =
      ((-Real.sin t * g : ℝ) : ℂ) + Complex.I * ((Real.cos t * g : ℝ) : ℂ) := by
    rw [Complex.exp_mul_I]
    push_cast
    linear_combination (Complex.sin (t : ℂ) * (g : ℂ)) * Complex.I_sq
  calc Complex.exp ((t : ℂ) * Complex.I) • (a + Complex.I • (g • b))
      = Complex.exp ((t : ℂ) * Complex.I) • a +
          (Complex.exp ((t : ℂ) * Complex.I) * (Complex.I * (g : ℂ))) • b := by
        rw [smul_add, ← Complex.coe_smul g b, smul_smul, smul_smul, mul_assoc]
    _ = ((Real.cos t : ℝ) : ℂ) • a + ((-Real.sin t * g : ℝ) : ℂ) • b +
          Complex.I • (((Real.sin t : ℝ) : ℂ) • a + ((Real.cos t * g : ℝ) : ℂ) • b) := by
        rw [e2, e1, add_smul, add_smul, smul_add, smul_smul, smul_smul]
        abel
    _ = _ := by simp only [Complex.coe_smul]

omit [CompleteSpace H] in
private theorem multiplier_ae (a : DifferentiableMultiplier I) (u : L2 H I) :
    a.multiplier u =ᵐ[volume] fun x => a.weight x • u x :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ u

omit [CompleteSpace H] in
private theorem derivativeMultiplier_ae (a : DifferentiableMultiplier I) (i : I) (u : L2 H I) :
    a.derivativeMultiplier i u =ᵐ[volume] fun x => a.gradient i x • u x :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ u

/-- The value and weak derivatives of the gauge-transformed vector. -/
def gaugePair (u : ElectronicH1Complex.ComplexH1 H I) :
    L2 H I × (I → L2 H I) :=
  (G.phaseL2 (ElectronicH1Complex.value u), fun i =>
    G.phaseL2 (ElectronicH1Complex.derivative i u +
      Complex.I • G.gradientMultiplier i (ElectronicH1Complex.value u)))

/-- As operators on L², `exp (i G) = cos G + i sin G`. -/
theorem phaseL2_eq_cos_sin (w : L2 H I) :
    G.phaseL2 w = G.cosMultiplier.multiplier w + Complex.I • G.sinMultiplier.multiplier w := by
  apply Lp.ext
  filter_upwards [G.phaseL2_ae w,
    Lp.coeFn_add (G.cosMultiplier.multiplier w) (Complex.I • G.sinMultiplier.multiplier w),
    Lp.coeFn_smul Complex.I (G.sinMultiplier.multiplier w),
    multiplier_ae G.cosMultiplier w, multiplier_ae G.sinMultiplier w] with x h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂, Pi.add_apply, h₃, Pi.smul_apply, h₄, h₅]
  exact factor_smul (G.fn x) _

/-- The derivative of `cos G` is `-(sin G) ∂ᵢ G`. -/
theorem cos_derivativeMultiplier (i : I) (w : L2 H I) :
    G.cosMultiplier.derivativeMultiplier i w =
      -G.sinMultiplier.multiplier (G.gradientMultiplier i w) := by
  apply Lp.ext
  filter_upwards [derivativeMultiplier_ae G.cosMultiplier i w,
    Lp.coeFn_neg (G.sinMultiplier.multiplier (G.gradientMultiplier i w)),
    multiplier_ae G.sinMultiplier (G.gradientMultiplier i w),
    G.gradientMultiplier_ae i w] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.neg_apply, h₃, h₄, G.cosMultiplier_gradient, mul_smul, neg_smul]
  rfl

/-- The derivative of `sin G` is `(cos G) ∂ᵢ G`. -/
theorem sin_derivativeMultiplier (i : I) (w : L2 H I) :
    G.sinMultiplier.derivativeMultiplier i w =
      G.cosMultiplier.multiplier (G.gradientMultiplier i w) := by
  apply Lp.ext
  filter_upwards [derivativeMultiplier_ae G.sinMultiplier i w,
    multiplier_ae G.cosMultiplier (G.gradientMultiplier i w),
    G.gradientMultiplier_ae i w] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, G.sinMultiplier_gradient, mul_smul]
  rfl

theorem gauge_value_eq (u : ElectronicH1Complex.ComplexH1 H I) :
    G.phaseL2 (ElectronicH1Complex.value u) =
      G.cosMultiplier.multiplier (ElectronicH1Complex.value u) +
        Complex.I • G.sinMultiplier.multiplier (ElectronicH1Complex.value u) :=
  G.phaseL2_eq_cos_sin _

theorem gauge_derivative_eq (u : ElectronicH1Complex.ComplexH1 H I) (i : I) :
    G.phaseL2 (ElectronicH1Complex.derivative i u +
        Complex.I • G.gradientMultiplier i (ElectronicH1Complex.value u)) =
      (G.cosMultiplier.multiplier (ElectronicH1Complex.derivative i u) +
          G.cosMultiplier.derivativeMultiplier i (ElectronicH1Complex.value u)) +
        Complex.I • (G.sinMultiplier.multiplier (ElectronicH1Complex.derivative i u) +
          G.sinMultiplier.derivativeMultiplier i (ElectronicH1Complex.value u)) := by
  rw [G.phaseL2_eq_cos_sin, G.cos_derivativeMultiplier, G.sin_derivativeMultiplier]
  simp only [map_add, map_smul, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

theorem gaugePair_mem (u : ElectronicH1Complex.ComplexH1 H I) :
    G.gaugePair u ∈ ElectronicH1Complex.complexWeakGraph H I := by
  let w := ElectronicH1Complex.realEquiv u
  let c := G.cosMultiplier.multiply w
  let s := G.sinMultiplier.multiply w
  have hc : c.val ∈ ElectronicH1Complex.complexWeakGraph H I := c.property
  have hs : s.val ∈ ElectronicH1Complex.complexWeakGraph H I := s.property
  have hsum := (ElectronicH1Complex.complexWeakGraph H I).add_mem hc
    ((ElectronicH1Complex.complexWeakGraph H I).smul_mem Complex.I hs)
  convert hsum using 1
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, Prod.smul_fst, ← ElectronicH1Space.value_apply,
      ← ElectronicH1Space.value_apply, DifferentiableMultiplier.value_multiply,
      DifferentiableMultiplier.value_multiply]
    exact G.gauge_value_eq u
  · funext i
    rw [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
      ← ElectronicH1Space.derivative_apply, ← ElectronicH1Space.derivative_apply,
      DifferentiableMultiplier.derivative_multiply, DifferentiableMultiplier.derivative_multiply]
    exact G.gauge_derivative_eq u i

/-- The gauge-transformed electronic H1 vector. -/
def gaugeH1Fun (u : ElectronicH1Complex.ComplexH1 H I) : ElectronicH1Complex.ComplexH1 H I :=
  ⟨G.gaugePair u, G.gaugePair_mem u⟩

@[simp] theorem value_gaugeH1Fun (u : ElectronicH1Complex.ComplexH1 H I) :
    ElectronicH1Complex.value (G.gaugeH1Fun u) = G.phaseL2 (ElectronicH1Complex.value u) := rfl

@[simp] theorem derivative_gaugeH1Fun (i : I) (u : ElectronicH1Complex.ComplexH1 H I) :
    ElectronicH1Complex.derivative i (G.gaugeH1Fun u) =
      G.phaseL2 (ElectronicH1Complex.derivative i u +
        Complex.I • G.gradientMultiplier i (ElectronicH1Complex.value u)) := rfl

theorem gaugeH1Fun_norm_le (u : ElectronicH1Complex.ComplexH1 H I) :
    ‖G.gaugeH1Fun u‖ ≤ (1 + |G.derivativeBound|) * ‖u‖ := by
  have hu : 0 ≤ ‖u‖ := norm_nonneg u
  have hD : 0 ≤ |G.derivativeBound| := abs_nonneg _
  rw [ElectronicH1Complex.norm_eq_max]
  apply max_le
  · rw [value_gaugeH1Fun, LinearIsometryEquiv.norm_map]
    exact (ElectronicH1Complex.norm_value_le u).trans (le_mul_of_one_le_left hu (by linarith))
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    change ‖ElectronicH1Complex.derivative i (G.gaugeH1Fun u)‖ ≤ _
    rw [derivative_gaugeH1Fun, LinearIsometryEquiv.norm_map]
    calc _ ≤ ‖ElectronicH1Complex.derivative i u‖ +
          ‖Complex.I • G.gradientMultiplier i (ElectronicH1Complex.value u)‖ := norm_add_le _ _
      _ ≤ ‖u‖ + |G.derivativeBound| * ‖u‖ := by
          rw [norm_smul, Complex.norm_I, one_mul]
          apply add_le_add (ElectronicH1Complex.norm_derivative_le u i)
          calc _ ≤ G.derivativeBound * ‖ElectronicH1Complex.value u‖ :=
                G.gradientMultiplier_norm_le i _
            _ ≤ |G.derivativeBound| * ‖ElectronicH1Complex.value u‖ :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
            _ ≤ |G.derivativeBound| * ‖u‖ :=
                mul_le_mul_of_nonneg_left (ElectronicH1Complex.norm_value_le u) hD
      _ = (1 + |G.derivativeBound|) * ‖u‖ := by ring

/-- The gauge transformation as a bounded complex-linear map of the H1 graph. -/
def gaugeH1 : ElectronicH1Complex.ComplexH1 H I →L[ℂ] ElectronicH1Complex.ComplexH1 H I :=
  LinearMap.mkContinuous
    { toFun := G.gaugeH1Fun
      map_add' := fun u v => by
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · change G.phaseL2 (ElectronicH1Complex.value (u + v)) =
            G.phaseL2 (ElectronicH1Complex.value u) + G.phaseL2 (ElectronicH1Complex.value v)
          rw [map_add, map_add]
        · funext i
          change G.phaseL2 (ElectronicH1Complex.derivative i (u + v) +
              Complex.I • G.gradientMultiplier i (ElectronicH1Complex.value (u + v))) =
            G.phaseL2 (ElectronicH1Complex.derivative i u +
              Complex.I • G.gradientMultiplier i (ElectronicH1Complex.value u)) +
            G.phaseL2 (ElectronicH1Complex.derivative i v +
              Complex.I • G.gradientMultiplier i (ElectronicH1Complex.value v))
          rw [← map_add]
          congr 1
          simp only [map_add, smul_add]
          abel
      map_smul' := fun c u => by
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · change G.phaseL2 (ElectronicH1Complex.value (c • u)) =
            c • G.phaseL2 (ElectronicH1Complex.value u)
          rw [map_smul, map_smul]
        · funext i
          change G.phaseL2 (ElectronicH1Complex.derivative i (c • u) +
              Complex.I • G.gradientMultiplier i (ElectronicH1Complex.value (c • u))) =
            c • G.phaseL2 (ElectronicH1Complex.derivative i u +
              Complex.I • G.gradientMultiplier i (ElectronicH1Complex.value u))
          simp only [map_smul]
          rw [smul_comm Complex.I c, ← smul_add, map_smul] }
    (1 + |G.derivativeBound|) G.gaugeH1Fun_norm_le

@[simp] theorem value_gaugeH1 (u : ElectronicH1Complex.ComplexH1 H I) :
    ElectronicH1Complex.value (G.gaugeH1 u) = G.phaseL2 (ElectronicH1Complex.value u) := rfl

@[simp] theorem derivative_gaugeH1 (i : I) (u : ElectronicH1Complex.ComplexH1 H I) :
    ElectronicH1Complex.derivative i (G.gaugeH1 u) =
      G.phaseL2 (ElectronicH1Complex.derivative i u +
        Complex.I • G.gradientMultiplier i (ElectronicH1Complex.value u)) := rfl

theorem phaseL2_neg (u : L2 H I) : G.neg.phaseL2 (G.phaseL2 u) = u := by
  have h := (phase (E := H) G.aestronglyMeasurable).symm_apply_apply u
  rw [phase_symm_apply] at h
  exact h

/-- The phase of `-G` undoes the gauge transformation on the H1 graph. -/
theorem gaugeH1_neg (u : ElectronicH1Complex.ComplexH1 H I) :
    G.neg.gaugeH1 (G.gaugeH1 u) = u := by
  apply ElectronicH1Complex.value_injective
  rw [value_gaugeH1, value_gaugeH1, phaseL2_neg]

theorem neg_neg_fn : G.neg.neg.fn = G.fn := by
  funext x
  exact neg_neg (G.fn x)

theorem gaugeH1_neg_left (u : ElectronicH1Complex.ComplexH1 H I) :
    G.gaugeH1 (G.neg.gaugeH1 u) = u := by
  apply ElectronicH1Complex.value_injective
  rw [value_gaugeH1, value_gaugeH1]
  apply Lp.ext
  filter_upwards [G.phaseL2_ae (G.neg.phaseL2 (ElectronicH1Complex.value u)),
    G.neg.phaseL2_ae (ElectronicH1Complex.value u)] with x h₁ h₂
  rw [h₁, h₂, smul_smul]
  have hx : factor G.fn x * factor G.neg.fn x = 1 := by
    have h := factor_neg_mul G.neg.fn x
    rw [show -G.neg.fn = G.fn from G.neg_neg_fn] at h
    exact h
  rw [hx, one_smul]

end GaugeFunction

end GptLean.TransformationsGauge
