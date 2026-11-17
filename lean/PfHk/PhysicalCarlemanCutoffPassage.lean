import PfHk.PhysicalCarlemanInput
import PfHk.SmoothCutoffOperations
import PfHk.CarlemanCutoffPassage

/-! Actual operator Carleman estimates pass through scalar annular
localization. The source is the proved physical commutator, split exactly
into the outer error and the disappearing inner error. -/

noncomputable section
namespace PfHk.PhysicalCarlemanInput

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalCutoffCommutator PfHk.PhysicalLocalEnergy
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFScalarMultiplier.multiply
  GptLean.ElectronicH1Multiplier.DifferentiableMultiplier.multiplier

variable {I : Type} [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

theorem commutator_sub (a b : TwiceDifferentiableMultiplier I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) :
    commutator V C κ hκ M hbound e A positive negative (twiceSub a b) u hu =
      commutator V C κ hκ M hbound e A positive negative a u hu -
        commutator V C κ hκ M hbound e A positive negative b u hu :=
  scalarCommutator_sub (H := PhotonFock) a b (inclusion I V u)
    (externalCovariant V C κ hκ M hbound e A positive negative u hu)

/-- The exact Fatou passage needed for the physical UCP argument.
Scalar annular support and cutoff convergence are visible, and the inner
source limit is an integral of the actual physical commutator. -/
theorem remove_annular_cutoff {E R inner α τ₀ K τ B : ℝ} {x₀ : Position I}
    (hCarleman : OperatorCarlemanAt V C κ hκ M hbound e A positive negative E x₀ R α τ₀ K)
    (hK : 0 ≤ K) (hτ : τ₀ ≤ τ) (hiR : inner ≤ R)
    (a : TwiceDifferentiableMultiplier I) (b : ℕ → TwiceDifferentiableMultiplier I)
    {u : Reference I V} {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (hsupp : ∀ n, AnnularSupport
      (inclusion I V (PhysicalPFScalarMultiplier.multiply V (twiceSub a (b n)).scalar u)) x₀ R)
    (hpoint : ∀ᵐ x ∂volume.restrict (Metric.ball x₀ inner), ∀ᶠ n in atTop,
      inclusion I V (PhysicalPFScalarMultiplier.multiply V (twiceSub a (b n)).scalar u) x =
        inclusion I V u x)
    (houter : Integrable (sourceIntegrand x₀ α τ
      (commutator V C κ hκ M hbound e A positive negative a u hu)) volume)
    (hinner : ∀ n, Integrable (sourceIntegrand x₀ α τ
      (commutator V C κ hκ M hbound e A positive negative (b n) u hu)) volume)
    (houterbound : (∫ x, sourceIntegrand x₀ α τ
      (commutator V C κ hκ M hbound e A positive negative a u hu) x) ≤ B)
    (herror : Tendsto (fun n => ∫ x, sourceIntegrand x₀ α τ
      (commutator V C κ hκ M hbound e A positive negative (b n) u hu) x) atTop (𝓝 0)) :
    (∫⁻ x in Metric.ball x₀ inner,
      ENNReal.ofReal (UniqueContinuation.radialMassIntegrand (fun x => dist x x₀)
        (inclusion I V u) α τ x)) ≤ ENNReal.ofReal (2 * K * B) := by
  let w := fun x : Position I =>
    Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist x x₀))) * dist x x₀ ^ 2
  let v := fun n => inclusion I V
    (PhysicalPFScalarMultiplier.multiply V (twiceSub a (b n)).scalar u)
  let source := fun c : TwiceDifferentiableMultiplier I =>
    commutator V C κ hκ M hbound e A positive negative c u hu
  apply CarlemanCutoffPassage.remove_inner_source (ν := volume)
    (F := fun n x => ENNReal.ofReal
      (UniqueContinuation.radialMassIntegrand (fun x => dist x x₀) (v n) α τ x))
    (w := w) (outer := source a) (inner := fun n => source (b n))
    (total := fun n => source (twiceSub a (b n))) hK
    (ae_of_all _ fun x => by dsimp [w]; positivity)
  · intro n
    exact (UniqueContinuation.radialMassIntegrand_measurable
      (Lp.stronglyMeasurable (v n)).norm.measurable
      (continuous_id.dist continuous_const).measurable α τ).ennreal_ofReal.aemeasurable
  · filter_upwards [hpoint] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hx] with n hn
    exact congrArg ENNReal.ofReal
      (congrArg (fun z : PhotonFock => τ ^ 3 *
        UniqueContinuation.weightedNormSq
          (fun y => CarlemanWeights.beta α (-Real.log (dist y x₀)) * dist y x₀ ^ (-2 : ℝ))
          (fun y => CarlemanWeights.weight α (-Real.log (dist y x₀)))
          (fun _ => z) τ x) hn.symm)
  · exact houter
  · exact hinner
  · intro n
    have hw : Measurable w := by unfold w CarlemanWeights.weight; fun_prop
    exact (hw.mul ((Lp.stronglyMeasurable (source (twiceSub a (b n)))).norm.measurable.pow_const 2)).aestronglyMeasurable
  · intro n
    have heq := commutator_sub V C κ hκ M hbound e A positive negative a (b n) u hu
    filter_upwards [Lp.coeFn_sub (source a) (source (b n))] with x hx
    exact (congrArg (fun z : WaveSpace I => z x) heq).trans hx
  · intro n
    have h := localized_eigenstate_estimate V C κ hκ M hbound e A positive negative
      hCarleman (twiceSub a (b n)) heigen (hsupp n) hτ
    have hl := lintegral_mono'
      (μ := volume.restrict (Metric.ball x₀ inner))
      (ν := volume.restrict (Metric.ball x₀ R)) (f := fun x => ENNReal.ofReal
      (UniqueContinuation.radialMassIntegrand (fun x => dist x x₀) (v n) α τ x))
      (Measure.restrict_mono (Metric.ball_subset_ball hiR) le_rfl) (le_refl _)
    exact (hl.trans h).trans (mul_le_mul' le_rfl
      (lintegral_mono' Measure.restrict_le_self (le_refl _)))
  · exact houterbound
  · exact herror

end PfHk.PhysicalCarlemanInput
