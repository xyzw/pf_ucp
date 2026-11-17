import PfHk.PauliWeakGaugeEnergy
import PfHk.PauliWeakGaugeData
import PfHk.PauliSpatialGauge
import PfHk.PauliCommonGroundState
import PfHk.WeakGaugeEnergy
import PfHk.GroundState

/-! The longitudinal identity for the actual spinful common ground state.
Weak phase transport gives the exact energy variation. Minimization for
every real scale forces its linear coefficient to vanish. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliGaugeVariation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPairSpace
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization GptLean.TransformationsGauge
  PfHk.PauliGroundState PfHk.PauliWeakGauge PfHk.PhysicalDiamagneticPotential
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] densityL1 currentL1 pairPotential
  SpatialGauge.shiftPair SpatialGauge.energyShift

private theorem variation_accounting {x y s p q r : ℝ}
    (hd : x - y = p - q) (hp : (0 + s) + q = 0 + r) :
    x = y + s + p - r := by linarith only [hd, hp]

private theorem variation_nonnegative {x y t J Y Z P : ℝ}
    (hle : x ≤ y)
    (he : y = x + (t * J + t ^ 2 * Y) + (P + t * Z) - P) :
    0 ≤ t * (J + Z) + t ^ 2 * Y := by
  linarith only [hle, he, show t * (J + Z) + t ^ 2 * Y =
    t * J + t ^ 2 * Y + t * Z by ring]

private theorem gauge_minimum (a : Potential) (d : Pair) (g : SpatialGauge)
    (E : ℝ) (Et : ℝ → ℝ) (hle : ∀ t, E ≤ Et t)
    (he : ∀ t, Et t = E + (PhysicalGroundState.Gauge.scale g t).energyShift d +
      pairPotential a ((PhysicalGroundState.Gauge.scale g t).shiftPair d) - pairPotential a d) :
    (∑ b, ∫ x, g.gradient b x * currentL1 d x b) +
      pairPotential a (g.shiftPair d - d) = 0 := by
  exact PhysicalGroundState.linear_zero
    (X := (∑ b, ∫ x, g.gradient b x * currentL1 d x b) + pairPotential a (g.shiftPair d - d))
    (Y := (1 / 2 : ℝ) * ∫ x, (∑ b, g.gradient b x ^ 2) * densityL1 d x)
    (fun t => by
      have ht := (he t).trans
        (congrArg (fun r : ℝ => r - pairPotential a d)
          (congrArg₂ (fun r s : ℝ => E + r + s)
            (PhysicalGroundState.Gauge.scale_energyShift g t d)
            (PhysicalGroundState.pairPotential_scale a g t d)))
      exact variation_nonnegative (hle t) ht)

private theorem stationarity_pairing {J p q : ℝ} (h₁ : J + p = 0) (h₂ : J + q = 0) :
    p = q := by linarith only [h₁, h₂]

private theorem density_inner_bound (A G : Vector) (r B : ℝ) (hG : ‖G‖ ≤ B) :
    ‖inner ℝ (E := Vector) A (r • G)‖ ≤ B * ‖r • A‖ := by
  rw [inner_smul_right, ← real_inner_smul_left]
  exact (norm_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left hG (norm_nonneg (r • A))).trans_eq (mul_comm _ _))

private theorem density_inner_difference (G A₁ A₂ : Vector) (r : ℝ) :
    inner ℝ (E := Vector) G (r • (A₁ - A₂)) = inner ℝ (E := Vector) A₁ (r • G) - inner ℝ (E := Vector) A₂ (r • G) := by
  simp only [inner_smul_right, inner_sub_right]
  rw [real_inner_comm G A₁, real_inner_comm G A₂]
  ring

private theorem divergence_from_pairing (a₁ a₂ : Potential) (d : Pair) (g : SpatialGauge)
    (hp : pairPotential a₁ (g.shiftPair d - d) = pairPotential a₂ (g.shiftPair d - d)) :
    (∫ x, inner ℝ (E := Vector) (g.gradientVector x) (vectorDifference a₁ a₂ d x)) = 0 := by
  have hp' := (PhysicalGroundState.pairPotential_shift a₁ g d).symm.trans
    (hp.trans (PhysicalGroundState.pairPotential_shift a₂ g d))
  have hint (a : Potential) : Integrable (fun x =>
      inner ℝ (E := Vector) (a.2.val x) (densityL1 d x • g.gradientVector x)) volume :=
    ((PhysicalGroundState.integrable_density_smul a d).norm.const_mul g.vectorBound).mono'
      (a.2.val.aestronglyMeasurable.inner
        ((Lp.aestronglyMeasurable (densityL1 d)).smul
          g.gradientVector_measurable.aestronglyMeasurable))
      (ae_of_all _ fun x => density_inner_bound (a.2.val x) (g.gradientVector x)
        (densityL1 d x) g.vectorBound (g.norm_gradientVector_le x))
  have hid : (∫ x, inner ℝ (E := Vector) (g.gradientVector x) (vectorDifference a₁ a₂ d x)) =
      (∫ x, inner ℝ (E := Vector) (a₁.2.val x) (densityL1 d x • g.gradientVector x)) -
        ∫ x, inner ℝ (E := Vector) (a₂.2.val x) (densityL1 d x • g.gradientVector x) :=
    (integral_congr_ae (ae_of_all _ fun x => density_inner_difference
      (g.gradientVector x) (a₁.2.val x) (a₂.2.val x) (densityL1 d x))).trans
      (integral_sub (hint a₁) (hint a₂))
  exact hid.trans (sub_eq_zero.mpr hp')

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (F : Frame) (χ : ArticleCutoff) (hN : 0 < N)

include hN

attribute [local irreducible] PauliGroundState.energy PauliGroundState.data
  GptLean.PhysicalPFReference.referenceSubspace PauliWeakGauge.gaugeState

theorem energy_variation (A : VectorPotential) (v : ScalarPotential) (c : ℝ)
    (hc : 0 ≤ c) (G : WeakSpatialGauge) (u : Ref N) :
    energy C e F χ A v c hc (gauge G u) = energy C e F χ A v c hc u +
      G.energyShift (data C e F χ u) +
      pairPotential (shifted v A) (G.shiftPair (data C e F χ u)) -
      pairPotential (shifted v A) (data C e F χ u) := by
  have hdiff := PauliGroundState.energy_difference C e F χ hN A (G.gaugeVector A) v v c hc (gauge G u)
  have hg := energy_gauge C e F χ A v c hc G u
  have hd := data_gauge C e F χ G u
  have hp := WeakGaugeEnergy.gauge_shifted_pairEnergy G v A (G.gaugeVector A)
    0 (data C e F χ u) (G.coeFn_gaugeVector A)
  have hdiff' := (congrArg (fun r : ℝ => energy C e F χ A v c hc (gauge G u) - r) hg).symm.trans
    (hdiff.trans (congrArg (fun d : Pair =>
      pairPotential (shifted v A) d - pairPotential (shifted v (G.gaugeVector A)) d) hd))
  exact variation_accounting hdiff' hp

theorem ground_gauge_zero (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (p : State N)
    (hp : IsGroundState C e F χ A v c hc p) (g : SpatialGauge) :
    (∑ a, ∫ x, g.gradient a x * currentL1 (data C e F χ p.vector) x a) +
      pairPotential (shifted v A) (g.shiftPair (data C e F χ p.vector) -
        data C e F χ p.vector) = 0 := by
  refine gauge_minimum (shifted v A) (data C e F χ p.vector) g
    (energy C e F χ A v c hc p.vector)
    (fun t => energy C e F χ A v c hc
      (gauge (ofSpatial (PhysicalGroundState.Gauge.scale g t)) p.vector)) ?_ ?_
  · intro t
    exact (hp (gaugeState (ofSpatial (PhysicalGroundState.Gauge.scale g t)) p)).trans_eq
      (congrArg (energy C e F χ A v c hc)
        (gaugeState_vector (ofSpatial (PhysicalGroundState.Gauge.scale g t)) p))
  · intro t
    exact (energy_variation C e F χ hN A v c hc
      (ofSpatial (PhysicalGroundState.Gauge.scale g t)) p.vector).trans
      (congrArg (fun r : ℝ => r - pairPotential (shifted v A) (data C e F χ p.vector))
        (congrArg₂ (fun r s : ℝ => energy C e F χ A v c hc p.vector + r + s)
          (ofSpatial_energyShift (PhysicalGroundState.Gauge.scale g t) (data C e F χ p.vector))
          (congrArg (pairPotential (shifted v A))
            (ofSpatial_shiftPair (PhysicalGroundState.Gauge.scale g t) (data C e F χ p.vector)))))

theorem vectorDifference_divergence
    (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (p₁ p₂ : State N)
    (h₁ : IsGroundState C e F χ A₁ v₁ c hc p₁)
    (h₂ : IsGroundState C e F χ A₂ v₂ c hc p₂)
    (hd : data C e F χ p₁.vector = data C e F χ p₂.vector)
    (g : SpatialGauge) :
    ∫ x, inner ℝ (E := Vector) (g.gradientVector x)
      (vectorDifference (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector) x) = 0 := by
  have hcommon := (PauliGroundState.common_ground_state C e F χ hN A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd).2.1
  have hg₁ := ground_gauge_zero C e F χ hN A₁ v₁ c hc p₁ h₁ g
  have hg₂ := ground_gauge_zero C e F χ hN A₂ v₂ c hc p₁ hcommon g
  exact divergence_from_pairing (shifted v₁ A₁) (shifted v₂ A₂)
    (data C e F χ p₁.vector) g (stationarity_pairing hg₁ hg₂)

end PfHk.PauliGaugeVariation

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
