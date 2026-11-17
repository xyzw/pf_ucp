import PfHk.PhysicalCutoffCommutator
import PfHk.PhysicalLocalEnergyCutoff
import PfHk.UniqueContinuation
import PfHk.ScalarCommutatorEstimate

/-! Pointwise and weighted integral estimates for the actual PF cutoff
commutator. Only scalar cutoff bounds enter the estimates. -/

noncomputable section
namespace PfHk.PhysicalCutoffCommutator

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy
open scoped InnerProductSpace Topology ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply
  roughMultiply externalCovariant

variable {I : Type} [Fintype I] [DecidableEq I]

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

theorem commutator_ae (a : TwiceDifferentiableMultiplier I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) :
    commutator V C κ hκ M hbound e A positive negative a u hu =ᵐ[volume] fun x =>
      (-Complex.I) • (∑ i, (a.scalar.gradient i x : ℂ) •
        externalCovariant V C κ hκ M hbound e A positive negative u hu i x) +
        (-(laplacian a x / 2) : ℂ) • inclusion I V u x := by
  exact scalar_commutator_ae (H := PhotonFock) a (inclusion I V u)
    (externalCovariant V C κ hκ M hbound e A positive negative u hu)

theorem commutator_norm_sq_ae (a : TwiceDifferentiableMultiplier I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) :
    ∀ᵐ x ∂volume,
      ‖commutator V C κ hκ M hbound e A positive negative a u hu x‖ ^ 2 ≤
        2 * (∑ i, a.scalar.gradient i x ^ 2) *
          (∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i x‖ ^ 2) +
        (1 / 2 : ℝ) * laplacian a x ^ 2 * ‖inclusion I V u x‖ ^ 2 := by
  exact scalar_commutator_norm_sq_ae (H := PhotonFock) a (inclusion I V u)
    (externalCovariant V C κ hκ M hbound e A positive negative u hu)

theorem weighted_commutator_bound (a : TwiceDifferentiableMultiplier I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    {s : Set (Position I)} (hs : MeasurableSet s) {w : Position I → ℝ}
    (hwm : AEStronglyMeasurable w volume) (hw0 : ∀ x, 0 ≤ w x)
    {W G L : ℝ} (hW : 0 ≤ W) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hw : ∀ x ∈ s, w x ≤ W)
    (hgrad : ∀ x ∈ s, ∑ i, a.scalar.gradient i x ^ 2 ≤ G)
    (hlap : ∀ x ∈ s, laplacian a x ^ 2 ≤ L)
    (houtgrad : ∀ x ∉ s, ∀ i, a.scalar.gradient i x = 0)
    (houtlap : ∀ x ∉ s, laplacian a x = 0) :
    Integrable (fun x => w x * ‖commutator V C κ hκ M hbound e A positive negative a u hu x‖ ^ 2)
      volume ∧
    (∫ x, w x * ‖commutator V C κ hκ M hbound e A positive negative a u hu x‖ ^ 2) ≤
      W * (2 * G * (∑ i, massOn s
        (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
          (1 / 2 : ℝ) * L * massOn s (inclusion I V u)) := by
  exact scalar_weighted_commutator_bound (H := PhotonFock) a (inclusion I V u)
    (externalCovariant V C κ hκ M hbound e A positive negative u hu)
    hs hwm hw0 hW hG hL hw hgrad hlap houtgrad houtlap

private theorem annulus_weight_bound {α τ ε r : ℝ} (hα : 0 < α)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hlo : ε ≤ r) (hhi : r ≤ 2 * ε)
    (hsmall : 2 * ε ≤ Real.exp (-2)) :
    Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log r)) * r ^ 2 ≤
      4 * ε ^ 2 * Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log ε)) := by
  have hphase : CarlemanWeights.weight α (-Real.log r) ≤
      CarlemanWeights.weight α (-Real.log ε) := by
    rcases hlo.eq_or_lt with heq | hlt
    · rw [heq]
    · exact (UniqueContinuation.radial_weight_gap hα hε hlt (hhi.trans hsmall)).le
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hphase (by positivity : 0 ≤ 2 * τ))
  have hrsq : r ^ 2 ≤ 4 * ε ^ 2 := by nlinarith
  calc
    _ ≤ Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log ε)) * (4 * ε ^ 2) :=
      mul_le_mul hexp hrsq (sq_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

private theorem massOn_mono {s t : Set (Position I)} (hst : s ⊆ t) (u : WaveSpace I) :
    massOn s u ≤ massOn t u := by
  exact setIntegral_mono_set (Lp.memLp u).norm.integrable_sq.integrableOn
    (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ hst)

theorem annular_commutator_integrable (a : TwiceDifferentiableMultiplier I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    (x₀ : Position I) {α τ r G L : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hr : 0 < r)
    (hsmall : 2 * r ≤ Real.exp (-2)) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hgrad : ∀ x, ∑ i, a.scalar.gradient i x ^ 2 ≤ G)
    (hlap : ∀ x, laplacian a x ^ 2 ≤ L)
    (houtgrad : ∀ x, x ∉ Metric.ball x₀ (2 * r) \ Metric.ball x₀ r →
      ∀ i, a.scalar.gradient i x = 0)
    (houtlap : ∀ x, x ∉ Metric.ball x₀ (2 * r) \ Metric.ball x₀ r → laplacian a x = 0) :
    Integrable (fun x =>
      Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist x x₀))) * dist x x₀ ^ 2 *
        ‖commutator V C κ hκ M hbound e A positive negative a u hu x‖ ^ 2) volume := by
  let w := fun x : Position I =>
    Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist x x₀))) * dist x x₀ ^ 2
  have hwm : AEStronglyMeasurable w volume := by
    apply Measurable.aestronglyMeasurable
    unfold w CarlemanWeights.weight
    fun_prop
  exact (weighted_commutator_bound V C κ hκ M hbound e A positive negative a u hu
    (s := Metric.ball x₀ (2 * r) \ Metric.ball x₀ r)
    (Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet)
    hwm (fun x => by dsimp [w]; positivity)
    (W := 4 * r ^ 2 * Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log r)))
    (by positivity) hG hL
    (fun x hx => annulus_weight_bound hα hτ hr
      (le_of_not_gt hx.2) hx.1.le hsmall)
    (fun x _ => hgrad x) (fun x _ => hlap x) houtgrad houtlap).1

/-- The displayed inner-error estimate in the paper, now for the actual
physical commutator and actual ball integrals. The cutoff assumptions contain
only its scalar derivatives and the annular support of those derivatives. -/
theorem inner_annulus_commutator_bound (a : TwiceDifferentiableMultiplier I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    (x₀ : Position I) {α τ ε G L : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (hsmall : 2 * ε ≤ Real.exp (-2)) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hgrad : ∀ x, ∑ i, a.scalar.gradient i x ^ 2 ≤ G / ε ^ 2)
    (hlap : ∀ x, laplacian a x ^ 2 ≤ L / ε ^ 4)
    (houtgrad : ∀ x, x ∉ Metric.ball x₀ (2 * ε) \ Metric.ball x₀ ε →
      ∀ i, a.scalar.gradient i x = 0)
    (houtlap : ∀ x, x ∉ Metric.ball x₀ (2 * ε) \ Metric.ball x₀ ε → laplacian a x = 0) :
    (∫ x, Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist x x₀))) *
      (dist x x₀) ^ 2 *
      ‖commutator V C κ hκ M hbound e A positive negative a u hu x‖ ^ 2) ≤
      Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log ε)) *
        (8 * G * (∑ i, massOn (Metric.ball x₀ (2 * ε))
          (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
          2 * L / ε ^ 2 * massOn (Metric.ball x₀ (2 * ε)) (inclusion I V u)) := by
  let s := Metric.ball x₀ (2 * ε) \ Metric.ball x₀ ε
  let w := fun x : Position I =>
    Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist x x₀))) * (dist x x₀) ^ 2
  let W := 4 * ε ^ 2 * Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log ε))
  have hwm : AEStronglyMeasurable w volume := by
    apply Measurable.aestronglyMeasurable
    unfold w CarlemanWeights.weight
    fun_prop
  have hb := weighted_commutator_bound V C κ hκ M hbound e A positive negative a u hu
    (s := s) (W := W) (G := G / ε ^ 2) (L := L / ε ^ 4)
    (Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet)
    hwm (fun x => by dsimp [w]; positivity) (by dsimp [W]; positivity)
    (by positivity) (by positivity) (by
      intro x hx
      exact annulus_weight_bound hα hτ hε
        (le_of_not_gt hx.2) hx.1.le hsmall)
    (fun x _ => hgrad x) (fun x _ => hlap x) houtgrad houtlap
  have hsum : (∑ i, massOn s
      (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) ≤
      ∑ i, massOn (Metric.ball x₀ (2 * ε))
        (externalCovariant V C κ hκ M hbound e A positive negative u hu i) :=
    Finset.sum_le_sum fun i _ => massOn_mono Set.sdiff_subset _
  have hmass := massOn_mono (s := s) Set.sdiff_subset (inclusion I V u)
  apply hb.2.trans
  calc
    _ ≤ W * (2 * (G / ε ^ 2) * (∑ i, massOn (Metric.ball x₀ (2 * ε))
        (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
          (1 / 2 : ℝ) * (L / ε ^ 4) * massOn (Metric.ball x₀ (2 * ε)) (inclusion I V u)) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [W]; positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity))
        (mul_le_mul_of_nonneg_left hmass (by positivity))
    _ = _ := by
      dsimp [W]
      field_simp
      ring

/-- The outer cutoff error has a coefficient independent of the Carleman
parameter. Its exponential rate is the phase at the inner edge of its annulus. -/
theorem outer_annulus_commutator_bound (a : TwiceDifferentiableMultiplier I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    (x₀ : Position I) {α τ R G L : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hR : 0 < R)
    (hsmall : R ≤ Real.exp (-2)) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hgrad : ∀ x, ∑ i, a.scalar.gradient i x ^ 2 ≤ G)
    (hlap : ∀ x, laplacian a x ^ 2 ≤ L)
    (houtgrad : ∀ x, x ∉ Metric.ball x₀ R \ Metric.ball x₀ (R / 2) →
      ∀ i, a.scalar.gradient i x = 0)
    (houtlap : ∀ x, x ∉ Metric.ball x₀ R \ Metric.ball x₀ (R / 2) → laplacian a x = 0) :
    (∫ x, Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist x x₀))) *
      (dist x x₀) ^ 2 *
      ‖commutator V C κ hκ M hbound e A positive negative a u hu x‖ ^ 2) ≤
      (R ^ 2 * (2 * G * (∑ i, massOn (Metric.ball x₀ R)
          (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
          (1 / 2 : ℝ) * L * massOn (Metric.ball x₀ R) (inclusion I V u))) *
        Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (R / 2))) := by
  let s := Metric.ball x₀ R \ Metric.ball x₀ (R / 2)
  let w := fun x : Position I =>
    Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist x x₀))) * (dist x x₀) ^ 2
  let W := R ^ 2 * Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (R / 2)))
  have hwm : AEStronglyMeasurable w volume := by
    apply Measurable.aestronglyMeasurable
    unfold w CarlemanWeights.weight
    fun_prop
  have hb := weighted_commutator_bound V C κ hκ M hbound e A positive negative a u hu
    (s := s) (W := W) (G := G) (L := L)
    (Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet)
    hwm (fun x => by dsimp [w]; positivity) (by dsimp [W]; positivity) hG hL (by
      intro x hx
      have hw := annulus_weight_bound hα hτ (half_pos hR)
        (le_of_not_gt hx.2) (by have hdist := Metric.mem_ball.mp hx.1; linarith) (by linarith)
      convert hw using 1 <;> dsimp [W, w] <;> ring)
    (fun x _ => hgrad x) (fun x _ => hlap x) houtgrad houtlap
  have hsum : (∑ i, massOn s
      (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) ≤
      ∑ i, massOn (Metric.ball x₀ R)
        (externalCovariant V C κ hκ M hbound e A positive negative u hu i) :=
    Finset.sum_le_sum fun i _ => massOn_mono Set.sdiff_subset _
  have hmass := massOn_mono (s := s) Set.sdiff_subset (inclusion I V u)
  calc
    _ ≤ W * (2 * G * (∑ i, massOn (Metric.ball x₀ R)
        (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
          (1 / 2 : ℝ) * L * massOn (Metric.ball x₀ R) (inclusion I V u)) :=
      hb.2.trans (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity))
          (mul_le_mul_of_nonneg_left hmass (by positivity))) (by dsimp [W]; positivity))
    _ = _ := by dsimp [W]; ring

end PfHk.PhysicalCutoffCommutator
