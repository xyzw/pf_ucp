import GptLean.PhysicalAttainmentFunctionals
import GptLean.TransformationsGaugeStates

/-!
Ground states of `H^{v,A}` on the article model, and the divergence of the
ground-state current density (`prop-ground-state-fields` (i)).

In shifted potential variables `a = (v + ½|A|², A)` the energy of a pure
state is `E(Ψ) + ⟨a, (ρ_Ψ, j_Ψ)⟩`, where `E` is the internal energy and
`j_Ψ` the combined current. A ground state attains the variational infimum
`shiftedGroundEnergy a`. Gauge covariance of `F_LL` along the gauges `t g`
makes `t ↦ E(Ψ) + ⟨a, ·⟩` at the gauged pair a quadratic polynomial bounded
below by its value at `t = 0`. Its linear coefficient is
`∫ ∇g · (j_Ψ + ρ_Ψ A)`, which therefore vanishes.
-/

noncomputable section

namespace GptLean.PhysicalGroundState

open MeasureTheory Filter PhysicalPairSpace PhysicalPairDuality TransformationsGauge
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

section Pairing

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure α}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [ENNReal.HolderConjugate q p]

/-- The pairing integrand of a potential with an intersection element is integrable. -/
theorem integrable_pairing (u : LpSum E q μ) (f : LpIntersection E 1 p μ) :
    Integrable (fun x => inner ℝ (u.val x) (fst f x)) μ := by
  have ha := integrable_inner (parts u).1 (fst f)
  have hb := integrable_inner (parts u).2 (snd f)
  refine (ha.add hb).congr ?_
  have hs : (u.val : α → E) =ᵐ[μ] fun x => (parts u).1 x + (parts u).2 x := by
    have h := congrArg (fun w : α →ₘ[μ] E => (w : α → E)) (parts_spec u)
    exact (Filter.EventuallyEq.of_eq h.symm).trans
      (AEEqFun.coeFn_add (parts u).1.val (parts u).2.val)
  filter_upwards [compatible f, hs] with x hf hx
  change inner ℝ ((parts u).1 x) (fst f x) + inner ℝ ((parts u).2 x) (snd f x) =
    inner ℝ (u.val x) (fst f x)
  rw [hx, inner_add_left, hf]

end Pairing

section Algebra

/-- A real quadratic bounded below by its value at zero has no linear term. -/
theorem linear_zero {X Y : ℝ} (h : ∀ t : ℝ, 0 ≤ t * X + t ^ 2 * Y) : X = 0 := by
  by_contra hX
  rcases lt_or_gt_of_ne hX with hneg | hpos
  · -- take a small positive t
    have hY : 0 ≤ Y ∨ Y < 0 := le_or_gt 0 Y
    let t : ℝ := -X / (2 * (|Y| + 1))
    have ht : 0 < t := div_pos (neg_pos.mpr hneg) (by positivity)
    have h1 := h t
    have hb : t * |Y| < -X / 2 := by
      have : t * (2 * (|Y| + 1)) = -X := div_mul_cancel₀ _ (by positivity)
      nlinarith [abs_nonneg Y]
    nlinarith [le_abs_self Y, sq_nonneg t]
  · let t : ℝ := -X / (2 * (|Y| + 1))
    have ht : t < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hpos) (by positivity)
    have h1 := h t
    have hb : -t * |Y| < X / 2 := by
      have : t * (2 * (|Y| + 1)) = -X := div_mul_cancel₀ _ (by positivity)
      nlinarith [abs_nonneg Y]
    nlinarith [le_abs_self Y, sq_nonneg t]

end Algebra

namespace Gauge

/-- The scaled gauge function `t g`. -/
def scale (g : SpatialGauge) (t : ℝ) : SpatialGauge where
  fn y := t * g.fn y
  differentiable := g.differentiable.const_mul t
  derivativeBound := |t| * g.derivativeBound
  derivative_bounded a y := by
    rw [fderiv_const_mul (g.differentiable y) t, smul_apply, smul_eq_mul,
      abs_mul]
    exact mul_le_mul_of_nonneg_left (g.derivative_bounded a y) (abs_nonneg t)

theorem scale_gradient (g : SpatialGauge) (t : ℝ) (a : Fin 3) (y : Position) :
    (scale g t).gradient a y = t * g.gradient a y := by
  change fderiv ℝ (fun z => t * g.fn z) y _ = _
  rw [fderiv_const_mul (g.differentiable y) t, smul_apply, smul_eq_mul]
  rfl

theorem scale_energyShift (g : SpatialGauge) (t : ℝ) (d : Pair) :
    (scale g t).energyShift d =
      t * (∑ a, ∫ x, g.gradient a x * currentL1 d x a) +
        t ^ 2 * ((1 / 2 : ℝ) * ∫ x, (∑ a, g.gradient a x ^ 2) * densityL1 d x) := by
  unfold SpatialGauge.energyShift
  simp only [scale_gradient, mul_pow, ← Finset.mul_sum, mul_assoc, integral_const_mul]
  ring

theorem scale_gradientVector (g : SpatialGauge) (t : ℝ) (y : Position) :
    (scale g t).gradientVector y = t • g.gradientVector y := by
  apply PiLp.ext
  intro a
  simp only [SpatialGauge.gradientVector_apply, PiLp.smul_apply, smul_eq_mul, scale_gradient]

private theorem vector_shift_algebra (j v w : Vector) (ρ t : ℝ) (hw : w = t • v) :
    j + ρ • w = j + t • ((j + ρ • v) - j) := by
  rw [hw, add_sub_cancel_left, smul_comm]

/-- The gauge shift of a pair is affine in the scale. -/
theorem shiftPair_scale (g : SpatialGauge) (t : ℝ) (d : Pair) :
    (scale g t).shiftPair d = d + t • (g.shiftPair d - d) := by
  have hR : densityL1 (d + t • (g.shiftPair d - d)) = densityL1 d :=
    (map_add _ _ _).trans ((congrArg (densityL1 d + ·) ((map_smul _ _ _).trans
      (congrArg (t • ·) ((map_sub _ _ _).trans
        (sub_eq_zero.mpr (g.densityL1_shiftPair d)))))).trans (by simp))
  have hm : currentL1 (d + t • (g.shiftPair d - d)) =
      currentL1 d + t • (currentL1 (g.shiftPair d) - currentL1 d) :=
    (map_add _ _ _).trans (congrArg (currentL1 d + ·) ((map_smul _ _ _).trans
      (congrArg (t • ·) (map_sub _ _ _))))
  apply pair_ext_ae
  · exact Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ 1 (volume : Measure Position) =>
      (f : Position → ℝ)) (((scale g t).densityL1_shiftPair d).trans hR.symm))
  · refine ((scale g t).currentL1_shiftPair d).trans (EventuallyEq.trans ?_
      (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp Vector 1 (volume : Measure Position) =>
        (f : Position → Vector)) hm.symm)))
    filter_upwards [g.currentL1_shiftPair d,
      Lp.coeFn_add (currentL1 d) (t • (currentL1 (g.shiftPair d) - currentL1 d)),
      Lp.coeFn_smul t (currentL1 (g.shiftPair d) - currentL1 d),
      Lp.coeFn_sub (currentL1 (g.shiftPair d)) (currentL1 d)] with x h₂ h₃ h₄ h₅
    refine Eq.trans ?_ (h₃.trans (congrArg (currentL1 d x + ·)
      (h₄.trans (congrArg (t • ·) (h₅.trans (congrArg (· - currentL1 d x) h₂)))))).symm
    exact vector_shift_algebra _ _ _ _ _ (scale_gradientVector g t x)

/-- The coordinate function `y ↦ y_b`, whose gradient is the unit vector `e_b`. -/
def coordinate (b : Fin 3) : SpatialGauge where
  fn y := y b
  differentiable := (EuclideanSpace.proj b : Position →L[ℝ] ℝ).differentiable
  derivativeBound := 1
  derivative_bounded a y := by
    have h : fderiv ℝ (fun y : Position => y b) y = EuclideanSpace.proj b :=
      (EuclideanSpace.proj b : Position →L[ℝ] ℝ).fderiv
    rw [h]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [Ne.symm hab]

theorem coordinate_gradientVector (b : Fin 3) (y : Position) :
    (coordinate b).gradientVector y = EuclideanSpace.single b 1 := by
  have h : fderiv ℝ (fun y : Position => y b) y = EuclideanSpace.proj b :=
    (EuclideanSpace.proj b : Position →L[ℝ] ℝ).fderiv
  apply PiLp.ext
  intro a
  rw [SpatialGauge.gradientVector_apply]
  change fderiv ℝ (fun y : Position => y b) y (EuclideanSpace.single a 1) = _
  rw [h]
  by_cases hab : a = b
  · subst hab
    simp
  · simp [hab, Ne.symm hab]

end Gauge

section Coupling

/-- The pairing of the vector potential with the gauge shift `ρ ∇g` of a pair. -/
theorem pairPotential_shift (a : Potential) (g : SpatialGauge) (d : Pair) :
    pairPotential a (g.shiftPair d - d) =
      ∫ x, inner ℝ (a.2.val x) (densityL1 d x • g.gradientVector x) := by
  rw [pairPotential_eq_integral]
  have hρ : (∫ x, a.1.val x * densityL1 (g.shiftPair d - d) x) = 0 := by
    have hm : densityL1 (g.shiftPair d - d) = 0 :=
      (map_sub _ _ _).trans (sub_eq_zero.mpr (g.densityL1_shiftPair d))
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [Filter.EventuallyEq.of_eq (congrArg
      (fun f : Lp ℝ 1 (volume : Measure Position) => (f : Position → ℝ)) hm),
      Lp.coeFn_zero ℝ 1 (volume : Measure Position)] with x h₁ hx
    rw [h₁, hx, Pi.zero_apply, mul_zero]
  rw [hρ, zero_add]
  apply integral_congr_ae
  have hm : currentL1 (g.shiftPair d - d) = currentL1 (g.shiftPair d) - currentL1 d := map_sub _ _ _
  filter_upwards [Filter.EventuallyEq.of_eq (congrArg
      (fun f : Lp Vector 1 (volume : Measure Position) => (f : Position → Vector)) hm),
    Lp.coeFn_sub (currentL1 (g.shiftPair d)) (currentL1 d),
    g.currentL1_shiftPair d] with x h₀ h₁ h₂
  exact congrArg (fun v : Vector => inner ℝ (a.2.val x) v)
    (h₀.trans (h₁.trans ((congrArg (· - currentL1 d x) h₂).trans (add_sub_cancel_left _ _))))

/-- The density times the vector potential is integrable: `ρ A ∈ L¹`. -/
theorem integrable_density_smul (a : Potential) (d : Pair) :
    Integrable (fun x => densityL1 d x • a.2.val x) volume := by
  have hcomp (b : Fin 3) : Integrable (fun x => densityL1 d x * a.2.val x b) volume := by
    have h := integrable_pairing (p := 3 / 2) a.2 ((Gauge.coordinate b).shiftPair d - d).2
    refine h.congr ?_
    have hm : currentL1 ((Gauge.coordinate b).shiftPair d - d) =
        currentL1 ((Gauge.coordinate b).shiftPair d) - currentL1 d := map_sub _ _ _
    have hc : (fst ((Gauge.coordinate b).shiftPair d - d).2 : Position → Vector) =ᵐ[volume]
        fun x => densityL1 d x • EuclideanSpace.single b 1 := by
      change (currentL1 ((Gauge.coordinate b).shiftPair d - d) : Position → Vector) =ᵐ[volume] _
      filter_upwards [Filter.EventuallyEq.of_eq (congrArg
          (fun f : Lp Vector 1 (volume : Measure Position) => (f : Position → Vector)) hm),
        Lp.coeFn_sub (currentL1 ((Gauge.coordinate b).shiftPair d)) (currentL1 d),
        (Gauge.coordinate b).currentL1_shiftPair d] with x h₀ h₁ h₂
      exact h₀.trans (h₁.trans ((congrArg (· - currentL1 d x) h₂).trans
        ((add_sub_cancel_left _ _).trans
          (congrArg (densityL1 d x • ·) (Gauge.coordinate_gradientVector b x)))))
    filter_upwards [hc] with x hx
    rw [hx, inner_smul_right, EuclideanSpace.inner_single_right]
    simp [mul_comm]
  have hm : AEStronglyMeasurable (fun x => densityL1 d x • a.2.val x) volume :=
    (Lp.aestronglyMeasurable (densityL1 d)).smul a.2.val.aestronglyMeasurable
  refine (integrable_finsetSum Finset.univ fun b _ => (hcomp b).norm).mono' hm ?_
  refine ae_of_all _ fun x => ?_
  calc
    ‖densityL1 d x • a.2.val x‖ ≤ ∑ b, ‖(densityL1 d x • a.2.val x) b‖ := by
      rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.norm_sq_eq]
      calc
        Real.sqrt (∑ b, ‖(densityL1 d x • a.2.val x) b‖ ^ 2) ≤
            Real.sqrt ((∑ b, ‖(densityL1 d x • a.2.val x) b‖) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _)
        _ = _ := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = ∑ b, ‖densityL1 d x * a.2.val x b‖ := by
      simp only [PiLp.smul_apply, smul_eq_mul]

end Coupling

variable {N : ℕ} (i : Fin N) (F : PhysicalPolarization.Frame)
  (χ : PhysicalPolarization.ArticleCutoff) (C : PhysicalFock.CanonicalSectorCCR PhysicalFock.photonMeasure)
  (B : PhysicalNormalTrace.StandardNormalTraceBackground)
  (S : PhysicalClosedForms.StandardClosedFormBackground) (e : ℝ)

/-- The pure-state model of the article. -/
abbrev model := PhysicalAttainment.pureModel i F χ C B S e

/-- Pure states of the article model. -/
abbrev State := PhysicalAttainmentFunctionals.PureState F χ C B S e (N := N)

/-- The energy `⟨Ψ, H^{v,A} Ψ⟩` in the shifted variables `a = (v + ½|A|², A)`. -/
def shiftedEnergy (a : Potential) (p : State F χ C B S e (N := N)) : ℝ :=
  (model i F χ C B S e).energy p + pairPotential a ((model i F χ C B S e).density p)

/-- `p` is a ground state of `H^{v,A}`: it minimizes the energy over all pure states. -/
def IsGroundState (a : Potential) (p : State F χ C B S e (N := N)) : Prop :=
  ∀ q, shiftedEnergy i F χ C B S e a p ≤ shiftedEnergy i F χ C B S e a q

/-- Ground states are exactly the pure states attaining the variational infimum. -/
theorem isGroundState_iff (a : Potential) (p : State F χ C B S e (N := N)) :
    IsGroundState i F χ C B S e a p ↔
      ((shiftedEnergy i F χ C B S e a p : ℝ) : EReal) =
        PhysicalAttainmentFunctionals.shiftedGroundEnergy i F χ C B S e a := by
  constructor
  · intro h
    exact le_antisymm (le_iInf fun q => EReal.coe_le_coe_iff.mpr (h q)) (iInf_le _ p)
  · intro h q
    have hq : PhysicalAttainmentFunctionals.shiftedGroundEnergy i F χ C B S e a ≤
        ((shiftedEnergy i F χ C B S e a q : ℝ) : EReal) := iInf_le _ q
    exact EReal.coe_le_coe_iff.mp (h.trans_le hq)

/-- A ground state bounds the pure search at every pair from below. -/
theorem ground_le_search {a : Potential} {p : State F χ C B S e (N := N)}
    (h : IsGroundState i F χ C B S e a p) (d : Pair) :
    ((shiftedEnergy i F χ C B S e a p - pairPotential a d : ℝ) : EReal) ≤
      DFT.search (model i F χ C B S e) d := by
  refine le_iInf₂ fun q hq => EReal.coe_le_coe_iff.mpr ?_
  have hq' := congrArg (pairPotential a) hq
  have h' := h q
  unfold shiftedEnergy at h' ⊢
  linarith

set_option hygiene false in
local notation "Kf" => PhysicalFock.PhysicalProfiles.momentumKernel (PhysicalPolarization.formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)

/-- Gauge covariance of the article's pure search. -/
theorem search_gauge (g : SpatialGauge) (d : Pair) :
    DFT.search (model i F χ C B S e) (g.shiftPair d) =
      DFT.search (model i F χ C B S e) d + ((g.energyShift d : ℝ) : EReal) :=
  g.search_gauge (PhysicalRemoval.potential N 1) C Kf
    (PhysicalFock.PhysicalProfiles.momentumKernel_continuous (PhysicalPolarization.formFactors F χ) rfl
      (LinearIsometryEquiv.refl ℝ _))
    (PhysicalFock.PhysicalProfiles.kernelBound (PhysicalPolarization.formFactors F χ) rfl
      (LinearIsometryEquiv.refl ℝ _))
    (PhysicalFock.PhysicalProfiles.momentumKernel_bound (PhysicalPolarization.formFactors F χ) rfl
      (LinearIsometryEquiv.refl ℝ _)) e i B S d

/-- The first-variation step in abstract form. -/
theorem first_variation {X Y Z P E S : ℝ} {s : EReal} {s' : ℝ → EReal} {L P' : ℝ → ℝ}
    (hS : S = E + P) (hs : s ≤ (E : EReal))
    (hlow : ∀ t, ((S - P' t : ℝ) : EReal) ≤ s' t) (hg : ∀ t, s' t = s + (L t : EReal))
    (hL : ∀ t, L t = t * X + t ^ 2 * Y) (hP : ∀ t, P' t = P + t * Z) : X + Z = 0 := by
  apply linear_zero (Y := Y)
  intro t
  have h := ((hlow t).trans_eq (hg t)).trans (add_le_add hs (le_refl _))
  rw [← EReal.coe_add, EReal.coe_le_coe_iff, hS, hP t, hL t] at h
  linarith [show t * (X + Z) + t ^ 2 * Y = t * X + t ^ 2 * Y + t * Z by ring]

/-- The pairing along the scaled gauges. -/
theorem pairPotential_scale (a : Potential) (g : SpatialGauge) (t : ℝ) (d : Pair) :
    pairPotential a ((Gauge.scale g t).shiftPair d) =
      pairPotential a d + t * pairPotential a (g.shiftPair d - d) := by
  rw [Gauge.shiftPair_scale, map_add, map_smul, smul_eq_mul]

/-- **First variation along gauges.** At a ground state, the linear gauge
coefficient vanishes: `∑ₐ ∫ ∂ₐ g jₐ + ⟨A, ρ ∇g⟩ = 0`. -/
theorem ground_gauge_zero {a : Potential} {p : State F χ C B S e (N := N)}
    (h : IsGroundState i F χ C B S e a p) (g : SpatialGauge) :
    (∑ b, ∫ x, g.gradient b x * currentL1 ((model i F χ C B S e).density p) x b) +
      pairPotential a (g.shiftPair ((model i F χ C B S e).density p) -
        (model i F χ C B S e).density p) = 0 :=
  first_variation
    (s' := fun t => DFT.search (model i F χ C B S e)
      ((Gauge.scale g t).shiftPair ((model i F χ C B S e).density p)))
    (L := fun t => (Gauge.scale g t).energyShift ((model i F χ C B S e).density p))
    (P' := fun t => pairPotential a ((Gauge.scale g t).shiftPair ((model i F χ C B S e).density p)))
    rfl (DFT.search_le _ rfl)
    (fun _ => ground_le_search i F χ C B S e h _)
    (fun t => search_gauge i F χ C B S e (Gauge.scale g t) _)
    (fun t => Gauge.scale_energyShift g t _)
    (fun t => pairPotential_scale a g t _)

/-- The divergence identity in integral form, for any pair. -/
theorem divergence_integral (a : Potential) (g : SpatialGauge) (d : Pair)
    (h : (∑ b, ∫ x, g.gradient b x * currentL1 d x b) +
      pairPotential a (g.shiftPair d - d) = 0) :
    ∫ x, inner ℝ (g.gradientVector x) (currentL1 d x + densityL1 d x • a.2.val x) = 0 := by
  have hρA := integrable_density_smul a d
  have hj : Integrable (fun x => currentL1 d x) volume := L1.integrable_coeFn _
  have hmeasg : AEStronglyMeasurable g.gradientVector volume :=
    g.gradientVector_measurable.aestronglyMeasurable
  have hint (f : Position → Vector) (hf : Integrable f volume) :
      Integrable (fun x => inner ℝ (g.gradientVector x) (f x)) volume :=
    (hf.norm.const_mul g.vectorBound).mono' (hmeasg.inner hf.1) (ae_of_all _ fun x =>
      (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (g.norm_gradientVector_le x) (norm_nonneg _)))
  have hcomp (b : Fin 3) : Integrable (fun x => g.gradient b x * currentL1 d x b) volume := by
    have hjb : Integrable (fun x => (EuclideanSpace.proj b : Vector →L[ℝ] ℝ) (currentL1 d x))
        volume := (EuclideanSpace.proj b : Vector →L[ℝ] ℝ).integrable_comp hj
    exact hjb.bdd_mul (g.gradient_measurable b).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact g.abs_gradient_le b x)
  have hX : (∫ x, inner ℝ (g.gradientVector x) (currentL1 d x)) =
      ∑ b, ∫ x, g.gradient b x * currentL1 d x b := by
    rw [← integral_finsetSum _ fun b _ => hcomp b]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [PiLp.inner_apply, SpatialGauge.gradientVector_apply, RCLike.inner_apply,
      conj_trivial]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hZ : (∫ x, inner ℝ (g.gradientVector x) (densityL1 d x • a.2.val x)) =
      pairPotential a (g.shiftPair d - d) := by
    rw [pairPotential_shift]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact (inner_smul_right _ _ _).trans ((congrArg (densityL1 d x * ·)
      (real_inner_comm (a.2.val x) (g.gradientVector x))).trans (inner_smul_right _ _ _).symm)
  have hsplit : (fun x => inner ℝ (g.gradientVector x) (currentL1 d x + densityL1 d x • a.2.val x)) =
      fun x => inner ℝ (g.gradientVector x) (currentL1 d x) +
        inner ℝ (g.gradientVector x) (densityL1 d x • a.2.val x) :=
    funext fun x => inner_add_right _ _ _
  rw [hsplit, integral_add (hint _ hj) (hint _ hρA), hX, hZ]
  exact h

/-- **`prop-ground-state-fields` (i).** The physical current `j = j_c + ρ A`
of a ground state is integrable and divergence-free: `∫ ∇g · j = 0` for
every gauge test function `g`, that is, every differentiable `g` with
bounded gradient, in particular every `g ∈ C_c^∞(ℝ³)`. -/
theorem ground_divergence {a : Potential} {p : State F χ C B S e (N := N)}
    (h : IsGroundState i F χ C B S e a p) (g : SpatialGauge) :
    Integrable (fun x => currentL1 ((model i F χ C B S e).density p) x +
      densityL1 ((model i F χ C B S e).density p) x • a.2.val x) volume ∧
    ∫ x, inner ℝ (g.gradientVector x) (currentL1 ((model i F χ C B S e).density p) x +
      densityL1 ((model i F χ C B S e).density p) x • a.2.val x) = 0 :=
  ⟨(L1.integrable_coeFn _).add (integrable_density_smul a _),
    divergence_integral a g _ (ground_gauge_zero i F χ C B S e h g)⟩

end GptLean.PhysicalGroundState
