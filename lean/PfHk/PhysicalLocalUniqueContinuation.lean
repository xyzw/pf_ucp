import PfHk.PhysicalCarlemanCutoffPassage
import PfHk.PhysicalCutoffGeometry
import PfHk.PhysicalCutoffInfiniteOrder

/-! The local continuation transfer from the physical operator Carleman
inequality. Scalar cutoffs are constructed, Caccioppoli controls the inner
error, Fatou removes it, and exponential separation gives a zero ball. -/

noncomputable section
namespace PfHk.PhysicalCarlemanInput

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalCutoffCommutator PfHk.PhysicalLocalEnergy PfHk.SmoothCutoffBounds
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFScalarMultiplier.multiply
  PhysicalPFReference.ordinary PhysicalPFReference.radiation externalCovariant massOn
  PfHk.PhysicalCutoffCommutator.commutator

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

/-- Local vanishing from an actual operator Carleman inequality and
infinite-order mass decay. No cutoff, derivative-energy decay, or singular
integrability is assumed in the conclusion's proof. -/
theorem flat_implies_zero_ball {E R α τ₀ K : ℝ} {x₀ : Position I}
    (hCarleman : OperatorCarlemanAt V C κ hκ M hbound e A positive negative E x₀ R α τ₀ K)
    (hα : 0 < α) (hR : 0 < R)
    (hRsmall : R ≤ Real.exp (-2)) (hK : 0 ≤ K)
    (hcoef : ∀ s, 0 < s → s ≤ R / 4 →
      1 ≤ CarlemanWeights.beta α (-Real.log s) * s ^ (-2 : ℝ))
    {u : Reference I V} {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hnegative : ScalarMultiplierBound negative (1 / 4) C₀)
    (hflat : InfiniteOrder.FlatAtZero
      (fun r => massOn (Metric.ball x₀ r) (inclusion I V u))) :
    ∀ᵐ x ∂volume.restrict (Metric.ball x₀ (R / 4)), inclusion I V u x = 0 := by
  classical
  let family := Classical.choice (exists_buffered_family x₀)
  let a := family.cutoff (R / 2)
  let G := (Fintype.card I : ℝ) * family.firstBound ^ 2
  let L := ((Fintype.card I : ℝ) * family.secondBound) ^ 2
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hL : 0 ≤ L := sq_nonneg _
  have hg (r : ℝ) (hr : 0 < r) (x : Position I) :
      (∑ i, (family.cutoff r).scalar.gradient i x ^ 2) ≤ G / r ^ 2 :=
    sum_gradient_sq_bound _ family.first_nonneg hr (family.first r hr) x
  have hl (r : ℝ) (hr : 0 < r) (x : Position I) :
      laplacian (family.cutoff r) x ^ 2 ≤ L / r ^ 4 :=
    sum_second_gradient_sq_bound _ family.second_nonneg hr (family.second r hr) x
  have hsg (r : ℝ) (hr : 0 < r) (x : Position I)
      (hx : x ∉ Metric.ball x₀ (2 * r) \ Metric.ball x₀ r) :
      ∀ i, (family.cutoff r).scalar.gradient i x = 0 :=
    (buffered_derivatives_supported _ hr (family.weight r hr) x hx).1
  have hsl (r : ℝ) (hr : 0 < r) (x : Position I)
      (hx : x ∉ Metric.ball x₀ (2 * r) \ Metric.ball x₀ r) :
      laplacian (family.cutoff r) x = 0 := by
    exact Finset.sum_eq_zero fun i _ =>
      (buffered_derivatives_supported _ hr (family.weight r hr) x hx).2 i i
  let ε : ℕ → ℝ := fun n => (R / 4) / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεR (n : ℕ) : ε n ≤ R / 4 := by
    exact (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
      (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; nlinarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (R / 4)
  have hεgt : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεlim, Eventually.of_forall hε⟩
  let b := fun n => family.cutoff (ε n)
  let Gout := G / (R / 2) ^ 2
  let Lout := L / (R / 2) ^ 4
  have hdouble : 2 * (R / 2) = R := by ring
  let Bout := R ^ 2 *
    (2 * Gout * (∑ i, massOn (Metric.ball x₀ R)
      (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
      (1 / 2 : ℝ) * Lout * massOn (Metric.ball x₀ R) (inclusion I V u))
  have hGout : 0 ≤ Gout := div_nonneg hG (sq_nonneg _)
  have hLout : 0 ≤ Lout := div_nonneg hL (pow_nonneg (half_pos hR).le _)
  have hBout : 0 ≤ Bout := by
    dsimp [Bout]
    exact mul_nonneg (sq_nonneg _) (add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hGout)
        (Finset.sum_nonneg fun _ _ => massOn_nonneg _ _))
      (mul_nonneg (mul_nonneg (by norm_num) hLout) (massOn_nonneg _ _)))
  have hsga : ∀ x, x ∉ Metric.ball x₀ R \ Metric.ball x₀ (R / 2) →
      ∀ i, a.scalar.gradient i x = 0 := by
    simpa only [hdouble] using hsg (R / 2) (half_pos hR)
  have hsla : ∀ x, x ∉ Metric.ball x₀ R \ Metric.ball x₀ (R / 2) → laplacian a x = 0 := by
    simpa only [hdouble] using hsl (R / 2) (half_pos hR)
  have hremoved (τ : ℝ) (hτ : max τ₀ 1 ≤ τ) :
      (∫⁻ x in Metric.ball x₀ (R / 4), ENNReal.ofReal
        (UniqueContinuation.radialMassIntegrand (fun x => dist x x₀) (inclusion I V u) α τ x)) ≤
      ENNReal.ofReal ((2 * K * Bout) * Real.exp
        (2 * τ * CarlemanWeights.weight α (-Real.log (R / 2)))) := by
    have hτ0 : 0 ≤ τ := zero_le_one.trans ((le_max_right _ _).trans hτ)
    have hoi := annular_commutator_integrable V C κ hκ M hbound e A positive negative a u hu x₀
      hα hτ0 (half_pos hR) (by simpa only [hdouble] using hRsmall) hGout hLout
      (hg (R / 2) (half_pos hR)) (hl (R / 2) (half_pos hR))
      (hsg (R / 2) (half_pos hR)) (hsl (R / 2) (half_pos hR))
    have hii (n : ℕ) := annular_commutator_integrable V C κ hκ M hbound e A positive negative
      (b n) u hu x₀ hα hτ0 (hε n) (by linarith [hεR n])
      (G := G / ε n ^ 2) (L := L / ε n ^ 4) (by positivity) (by positivity)
      (hg (ε n) (hε n)) (hl (ε n) (hε n))
      (hsg (ε n) (hε n)) (hsl (ε n) (hε n))
    have hob := outer_annulus_commutator_bound V C κ hκ M hbound e A positive negative a u hu x₀
      hα hτ0 hR hRsmall hGout hLout
      (hg (R / 2) (half_pos hR)) (hl (R / 2) (half_pos hR)) hsga hsla
    have hilim := eigenstate_inner_commutator_tendsto V C κ hκ M hbound e A positive negative
      family.cutoff u hu x₀ heigen C₀ hnegative
      (fun r => bufferedBallCutoff family r r.property.1)
      hα hτ0 hG hL (half_pos hR) (by simpa only [hdouble] using hRsmall)
      (fun r hr _ => hg r hr) (fun r hr _ => hl r hr)
      (fun r hr _ => hsg r hr) (fun r hr _ => hsl r hr) hflat
    have hh := remove_annular_cutoff V C κ hκ M hbound e A positive negative
      hCarleman hK ((le_max_left _ _).trans hτ) (by linarith : R / 4 ≤ R) a b heigen
      (fun n => buffered_annular_support V u hR (hε n) (hεR n) a (b n)
        (family.weight (R / 2) (half_pos hR)) (family.weight (ε n) (hε n)))
      (buffered_cutoff_eventually_identity V u hR (by linarith : R / 4 ≤ R / 2)
        a b ε hε hεlim (family.weight (R / 2) (half_pos hR))
        (fun n => family.weight (ε n) (hε n))) hoi hii hob (hilim.comp hεgt)
    convert hh using 1
    congr 1
    ring
  apply UniqueContinuation.ae_zero_of_radial_lintegral_outer_error hα
    (by positivity : 0 < R / 4) (by linarith : R / 4 < R / 2)
    (by linarith : R / 2 ≤ Real.exp (-2)) (by positivity : 0 ≤ 2 * K * Bout)
    (r := fun x => dist x x₀) (τ₀ := τ₀)
  · have hnot : ∀ᵐ x : Position I ∂volume, x ≠ x₀ := by
      simpa only [Set.mem_singleton_iff] using
        (measure_eq_zero_iff_ae_notMem.mp (measure_singleton x₀))
    filter_upwards [ae_restrict_of_ae hnot,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxb
    exact ⟨dist_pos.mpr hx, hxb⟩
  · exact hcoef
  · exact (Lp.memLp (inclusion I V u)).norm.integrable_sq.integrableOn
  · intro τ _
    exact (UniqueContinuation.radialMassIntegrand_measurable
      (Lp.stronglyMeasurable (inclusion I V u)).norm.measurable
      (continuous_id.dist continuous_const).measurable α τ).aestronglyMeasurable
  · exact hremoved

end PfHk.PhysicalCarlemanInput
