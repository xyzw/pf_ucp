import PfHk.PhysicalLocalEnergySobolev
import PfHk.PhysicalLocalEnergyBallCutoff
import GptLean.ElectronicLocalization

/-! Ball-cutoff form of the physical local-energy estimate. The cutoff
data below concerns only a real scalar function and its ordinary first
derivatives. No physical energy inequality occurs in the cutoff data. -/

noncomputable section

namespace PfHk.PhysicalLocalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply

variable {I : Type} [Fintype I] [DecidableEq I]

def massOn (s : Set (Position I)) (u : WaveSpace I) : ℝ := ∫ x in s, ‖u x‖ ^ 2

theorem massOn_nonneg (s : Set (Position I)) (u : WaveSpace I) : 0 ≤ massOn s u :=
  integral_nonneg fun _ => sq_nonneg _

attribute [local irreducible] massOn

private theorem multiplier_ae (a : DifferentiableMultiplier I) (u : WaveSpace I) :
    a.multiplier (H := PhotonFock) u =ᵐ[volume] fun x => a.weight x • u x :=
  PhotonLocalization.realL2Multiplier_apply a.weight
    a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded) u

private theorem derivativeMultiplier_ae (a : DifferentiableMultiplier I) (i : I) (u : WaveSpace I) :
    a.derivativeMultiplier (H := PhotonFock) i u =ᵐ[volume] fun x => a.gradient i x • u x :=
  PhotonLocalization.realL2Multiplier_apply (a.gradient i)
    (a.gradient_measurable i).aestronglyMeasurable a.derivativeBound
    (ae_of_all _ (a.derivative_bounded i)) u

attribute [local irreducible] DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier

private theorem localization_scalar_bound (c d L r m a b : ℝ)
    (hc : 0 ≤ c) (hr : 0 < r) (hr1 : r ≤ 1) (hm : 0 ≤ m)
    (ha : a ≤ m) (hb : b ≤ d * (L / r) ^ 2 * m) :
    8 * (c * a + (1 / 2 : ℝ) * b) ≤ (8 * c + 4 * d * L ^ 2) / r ^ 2 * m := by
  have hs : r ^ 2 ≤ 1 := by nlinarith only [hr, hr1]
  have hca := mul_le_mul_of_nonneg_left ha hc
  have hdiv : c * m ≤ c / r ^ 2 * m := by
    apply mul_le_mul_of_nonneg_right _ hm
    exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr (mul_le_of_le_one_right hc hs)
  have halg : (8 * c + 4 * d * L ^ 2) / r ^ 2 * m =
      8 * (c / r ^ 2 * m + (1 / 2 : ℝ) * (d * (L / r) ^ 2 * m)) := by
    field_simp [hr.ne']
    <;> ring
  rw [halg]
  linarith

private theorem cutoff_value_inside {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [NormedSpace ℂ H] (w b : ℝ) (c : ℂ) (z ψ : H)
    (hw : w = 1) (hb : b = 0) : w • z + c • (b • ψ) = z := by
  simp only [hw, hb, one_smul, zero_smul, smul_zero, add_zero]

theorem supported_multiplier_norm_sq (s : Set (Position I)) (hs : MeasurableSet s)
    (f : Position I → ℝ) (L : ℝ) (u z : WaveSpace I)
    (hz : z =ᵐ[volume] fun x => f x • u x)
    (hf : ∀ x, |f x| ≤ L) (hout : ∀ x ∉ s, f x = 0) :
    ‖z‖ ^ 2 ≤ L ^ 2 * massOn s u := by
  rw [l2_norm_sq, massOn, ← integral_const_mul,
    ← integral_indicator hs]
  apply integral_mono_ae (Lp.memLp z).norm.integrable_sq
    (((Lp.memLp u).norm.integrable_sq.const_mul (L ^ 2)).indicator hs)
  filter_upwards [hz] with x hx
  apply ((congrArg (fun v : PhotonFock => ‖v‖ ^ 2) hx).trans
    (real_smul_norm_sq (f x) (u x))).le.trans
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs]
    have hb : f x ^ 2 ≤ L ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f x)) (hf x) 2
    exact mul_le_mul_of_nonneg_right
      hb (sq_nonneg _)
  · rw [Set.indicator_of_notMem hxs, hout x hxs]
    simp

theorem BallCutoff.mass_bound {x₀ : Position I} {r L : ℝ}
    (a : BallCutoff x₀ r L) (u : WaveSpace I) :
    ‖a.multiplier.multiplier u‖ ^ 2 ≤ massOn (Metric.ball x₀ (2 * r)) u := by
  have h := supported_multiplier_norm_sq (Metric.ball x₀ (2 * r)) measurableSet_ball
    a.multiplier.weight 1 u (a.multiplier.multiplier u)
    (multiplier_ae a.multiplier u)
    (fun x => by rw [abs_of_nonneg (a.nonneg x)]; exact a.le_one x) a.eq_zero
  simpa using h

theorem BallCutoff.gradient_zero_outside {x₀ : Position I} {r L : ℝ}
    (a : BallCutoff x₀ r L) (i : I) (x : Position I)
    (hx : x ∉ Metric.ball x₀ (2 * r)) : a.multiplier.gradient i x = 0 := by
  unfold DifferentiableMultiplier.gradient
  rw [ElectronicLocalization.fderiv_eq_zero_of_nonneg a.nonneg (a.eq_zero x hx)]
  rfl

theorem BallCutoff.gradient_zero_inside {x₀ : Position I} {r L : ℝ}
    (a : BallCutoff x₀ r L) (i : I) (x : Position I)
    (hx : x ∈ Metric.ball x₀ r) : a.multiplier.gradient i x = 0 := by
  have hm : IsLocalMax a.multiplier.weight x :=
    Filter.Eventually.of_forall fun y => by rw [a.eq_one x hx]; exact a.le_one y
  unfold DifferentiableMultiplier.gradient
  rw [hm.fderiv_eq_zero]
  rfl

theorem massOn_le_of_ae_eq (s : Set (Position I)) (hs : MeasurableSet s)
    (u v : WaveSpace I) (h : ∀ᵐ x ∂volume, x ∈ s → u x = v x) :
    massOn s u ≤ ‖v‖ ^ 2 := by
  calc
    _ = ∫ x in s, ‖v x‖ ^ 2 := by
      unfold massOn
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hs] with x hx hxs
      rw [hx hxs]
    _ ≤ ∫ x, ‖v x‖ ^ 2 := setIntegral_le_integral (Lp.memLp v).norm.integrable_sq
      (ae_of_all _ fun _ => sq_nonneg _)
    _ = ‖v‖ ^ 2 := (l2_norm_sq v).symm

/-- The cutoff equals one and its gradient vanishes on the inner ball,
so its localized derivative controls the original derivative there. -/
theorem BallCutoff.local_norm_bound {x₀ : Position I} {r L : ℝ}
    (a : BallCutoff x₀ r L) (i : I) (c : ℂ) (ψ z localized : WaveSpace I)
    (hlocal : localized = a.multiplier.multiplier z +
      c • a.multiplier.derivativeMultiplier i ψ) :
    massOn (Metric.ball x₀ r) z ≤ ‖localized‖ ^ 2 := by
  apply massOn_le_of_ae_eq (Metric.ball x₀ r) measurableSet_ball
  filter_upwards [Lp.coeFn_add (a.multiplier.multiplier z)
      (c • a.multiplier.derivativeMultiplier i ψ),
    Lp.coeFn_smul c (a.multiplier.derivativeMultiplier i ψ),
    multiplier_ae a.multiplier z, derivativeMultiplier_ae a.multiplier i ψ]
    with x h₁ h₂ h₃ h₄
  intro hx
  simp only [Pi.add_apply, Pi.smul_apply] at h₁ h₂
  have he := (congrArg (fun v : WaveSpace I => v x) hlocal).trans
    (h₁.trans (congrArg₂ (fun v w : PhotonFock => v + w) h₃
      (h₂.trans (congrArg (fun v : PhotonFock => c • v) h₄))))
  exact (he.trans (cutoff_value_inside _ _ c (z x) (ψ x)
    (a.eq_one x hx) (a.gradient_zero_inside i x hx))).symm

theorem BallCutoff.local_multiplier_bound {x₀ : Position I} {r L : ℝ}
    (a : BallCutoff x₀ r L) (z localized : WaveSpace I)
    (hlocal : localized = a.multiplier.multiplier z) :
    massOn (Metric.ball x₀ r) z ≤ ‖localized‖ ^ 2 := by
  apply massOn_le_of_ae_eq (Metric.ball x₀ r) measurableSet_ball
  rw [hlocal]
  filter_upwards [multiplier_ae a.multiplier z] with x hx
  intro hxs
  rw [hx, a.eq_one x hxs, one_smul]

theorem BallCutoff.error_bound {x₀ : Position I} {r L : ℝ}
    (a : BallCutoff x₀ r L) (u : WaveSpace I) :
    (∑ i, ‖a.multiplier.derivativeMultiplier i u‖ ^ 2) ≤
      Fintype.card I * (L / r) ^ 2 * massOn (Metric.ball x₀ (2 * r)) u := by
  calc
    _ ≤ ∑ _i : I, (L / r) ^ 2 * massOn (Metric.ball x₀ (2 * r)) u := by
      apply Finset.sum_le_sum
      intro i _
      exact supported_multiplier_norm_sq (Metric.ball x₀ (2 * r)) measurableSet_ball
        (a.multiplier.gradient i) (L / r) u (a.multiplier.derivativeMultiplier i u)
        (derivativeMultiplier_ae a.multiplier i u)
        (a.gradient_bound i) (a.gradient_zero_outside i)
    _ = _ := by simp [mul_assoc]

attribute [local irreducible] externalCovariant externalEnergy normGradientEnergy roughMultiply

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

theorem energy_on_ball_le_localized (u : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    {x₀ : Position I} {r L : ℝ} (a : BallCutoff x₀ r L) :
    (∑ i, massOn (Metric.ball x₀ r) (ordinary I V i u)) +
      (∑ i, massOn (Metric.ball x₀ r)
        (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
      massOn (Metric.ball x₀ r) (radiation I V u) ≤
    (∑ i, ‖ordinary I V i (PhysicalPFScalarMultiplier.multiply V a.multiplier u)‖ ^ 2) +
      (∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative
        (PhysicalPFScalarMultiplier.multiply V a.multiplier u) (hu.localize V a.multiplier) i‖ ^ 2) +
      ‖radiation I V (PhysicalPFScalarMultiplier.multiply V a.multiplier u)‖ ^ 2 := by
  apply add_le_add
  · apply add_le_add
    · apply Finset.sum_le_sum
      intro i _
      apply a.local_norm_bound i 1 (inclusion I V u)
      simpa only [one_smul] using PhysicalPFScalarMultiplier.ordinary_multiply V a.multiplier u i
    · apply Finset.sum_le_sum
      intro i _
      exact a.local_norm_bound i (-Complex.I) (inclusion I V u) _ _
        (externalCovariant_localize V C κ hκ M hbound e A positive negative u hu a.multiplier i)
  · exact a.local_multiplier_bound _ _ (PhysicalPFScalarMultiplier.radiation_multiply V a.multiplier u)

/-- The localized norm-gradient form required in the density-point
iteration, with a constant independent of the ball center and radius. -/
theorem caccioppoli_localized {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hSob : ScalarMultiplierBound negative (1 / 4) C₀)
    {x₀ : Position I} {r L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (a : BallCutoff x₀ r L) :
    (∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a.multiplier u) (hu.localize V a.multiplier) i‖ ^ 2) +
      ‖radiation I V (PhysicalPFScalarMultiplier.multiply V a.multiplier u)‖ ^ 2 +
      normGradientEnergy V (PhysicalPFScalarMultiplier.multiply V a.multiplier u) ≤
      (8 * (|E| + |C₀|) + 4 * (Fintype.card I) * L ^ 2) / r ^ 2 *
        massOn (Metric.ball x₀ (2 * r)) (inclusion I V u) := by
  have he := localized_covariant_energy V C κ hκ M hbound e A positive negative
    heigen C₀ hSob a.multiplier
  exact he.trans (localization_scalar_bound (|E| + |C₀|) (Fintype.card I) L r
    _ _ _ (add_nonneg (abs_nonneg _) (abs_nonneg _)) hr hr1
    (massOn_nonneg _ _) (a.mass_bound _) (a.error_bound _))

theorem caccioppoli_normGradient {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hSob : ScalarMultiplierBound negative (1 / 4) C₀)
    {x₀ : Position I} {r L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (a : BallCutoff x₀ r L) :
    normGradientEnergy V (PhysicalPFScalarMultiplier.multiply V a.multiplier u) ≤
      (8 * (|E| + |C₀|) + 4 * (Fintype.card I) * L ^ 2) / r ^ 2 *
        massOn (Metric.ball x₀ (2 * r)) (inclusion I V u) := by
  have h := caccioppoli_localized V C κ hκ M hbound e A positive negative
    heigen C₀ hSob hr hr1 a
  have hc : 0 ≤ ∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a.multiplier u) (hu.localize V a.multiplier) i‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hr := sq_nonneg ‖radiation I V (PhysicalPFScalarMultiplier.multiply V a.multiplier u)‖
  linarith

/-- The physical Caccioppoli estimate controls covariant derivatives,
ordinary derivatives and the radiation square root on the inner ball. -/
theorem caccioppoli {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ C_A : ℝ) (hSob : ScalarMultiplierBound negative (1 / 4) C₀)
    (hA : ∀ i, ScalarMultiplierBound (A i) 1 C_A)
    {x₀ : Position I} {r L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (a : BallCutoff x₀ r L) :
    (∑ i, massOn (Metric.ball x₀ r) (ordinary I V i u)) +
      (∑ i, massOn (Metric.ball x₀ r)
        (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
      massOn (Metric.ball x₀ r) (radiation I V u) ≤
    (derivativeRecoveryFactor (Fintype.card I) e M * (8 * (|E| + |C₀|) + 4 * (Fintype.card I) * L ^ 2) +
        derivativeMassFactor (Fintype.card I) e M C_A) / r ^ 2 *
      massOn (Metric.ball x₀ (2 * r)) (inclusion I V u) := by
  let F := derivativeRecoveryFactor (Fintype.card I) e M
  let B := derivativeMassFactor (Fintype.card I) e M C_A
  let K := 8 * (|E| + |C₀|) + 4 * (Fintype.card I) * L ^ 2
  let m := massOn (Metric.ball x₀ (2 * r)) (inclusion I V u)
  have hF : 0 ≤ F := derivativeRecoveryFactor_nonneg (Fintype.card I) e M
  have hB : 0 ≤ B := derivativeMassFactor_nonneg (Fintype.card I) e M C_A
  have hm : 0 ≤ m := massOn_nonneg _ _
  have hcore := caccioppoli_localized V C κ hκ M hbound e A positive negative
    heigen C₀ hSob hr hr1 a
  have hfull := full_energy_bound V C κ hκ M hbound e A positive negative C_A hA
    (PhysicalPFScalarMultiplier.multiply V a.multiplier u) (hu.localize V a.multiplier)
  have hmass := (congrArg (fun z : WaveSpace I => ‖z‖ ^ 2)
    (PhysicalPFScalarMultiplier.value_multiply V a.multiplier u)).le.trans
      (a.mass_bound (inclusion I V u))
  have hscaled : B * m ≤ B / r ^ 2 * m := by
    apply mul_le_mul_of_nonneg_right _ hm
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    exact mul_le_of_le_one_right hB (by nlinarith only [hr, hr1])
  have hupper := add_le_add (mul_le_mul_of_nonneg_left hcore hF)
    (mul_le_mul_of_nonneg_left hmass hB)
  have hlocal := energy_on_ball_le_localized V C κ hκ M hbound e A positive negative u hu a
  have hcombined :
      (∑ i, massOn (Metric.ball x₀ r) (ordinary I V i u)) +
        (∑ i, massOn (Metric.ball x₀ r)
          (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
        massOn (Metric.ball x₀ r) (radiation I V u) ≤
      F * (K / r ^ 2 * m) + B / r ^ 2 * m :=
    hlocal.trans (hfull.trans (hupper.trans (add_le_add le_rfl hscaled)))
  exact hcombined.trans_eq (by dsimp [F, B, K, m]; ring)

end PfHk.PhysicalLocalEnergy
