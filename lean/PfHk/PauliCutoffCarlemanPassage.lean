import PfHk.PauliOperatorCarlemanMass
import PfHk.PauliScalarSobolev
import PfHk.PhysicalCutoffGeometry

/-! The actual bundled cutoff source passes through Fatou's lemma.
No integrability at the singular center is assumed. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PauliOperatorCarleman

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PauliLocalEnergy
  PfHk.PhysicalCommonFormDomain PfHk.CenteredPhysicalReference
  PfHk.PhysicalCutoffCommutator PfHk.SmoothCutoffBounds
  PfHk.PhysicalFieldRegularity PfHk.PhysicalLocalEnergy
  PfHk.PhysicalCarlemanInput
open scoped ENNReal Topology

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

attribute [local irreducible] referenceSubspace inclusion

private theorem bundle_sub {X T H : Type*} [MeasurableSpace X] [Fintype T]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    (f g : T → Lp H 2 μ) :
    FiniteFiberL2.bundle (f - g) = FiniteFiberL2.bundle f - FiniteFiberL2.bundle g := by
  have hn : FiniteFiberL2.bundle (-g) = -FiniteFiberL2.bundle g := by
    simpa only [neg_one_smul] using FiniteFiberL2.bundle_smul (-1 : ℂ) g
  simpa only [sub_eq_add_neg, hn] using FiniteFiberL2.bundle_add f (-g)

variable {N : ℕ}
variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

theorem commutator_sub (a b : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N) :
    commutator F χ C e A v c hc (twiceSub a b) u =
      commutator F χ C e A v c hc a u - commutator F χ C e A v c hc b u := by
  have h : PauliLocalCutoffRules.commutator C (profile F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
      (vector A) (positive v c) (negative v c) (twiceSub a b) u (physicalDomain A v c hc u) =
      PauliLocalCutoffRules.commutator C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
        (vector A) (positive v c) (negative v c) a u (physicalDomain A v c hc u) -
      PauliLocalCutoffRules.commutator C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
        (vector A) (positive v c) (negative v c) b u (physicalDomain A v c hc u) := by
    funext s
    exact PhysicalCarlemanInput.commutator_sub (fun _ => 0) C (profile F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
      (vector A) (positive v c) (negative v c) a b (u s) (physicalDomain A v c hc u s)
  exact (congrArg FiniteFiberL2.bundle h).trans (bundle_sub _ _)

attribute [local irreducible] commutator

/-- Finite spin coupling is retained throughout removal of the inner cutoff. -/
theorem remove_annular_cutoff [Nonempty (Fin N × Fin 3)]
    {E R α τ₀ K τ B : ℝ} {O : Configuration N}
    (hCarleman : CarlemanAt F χ C e A v c hc E O R α τ₀ K)
    (hK : 0 ≤ K) (hτ : τ₀ ≤ τ) (hR : 0 < R)
    (family : BufferedFamily O) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hεR : ∀ n, ε n ≤ R / 4)
    (hεlim : Tendsto ε atTop (𝓝 0))
    {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u))
    (houter : Integrable (sourceIntegrand O α τ
      (commutator F χ C e A v c hc (family.cutoff (R / 2)) u)))
    (hinner : ∀ n, Integrable (sourceIntegrand O α τ
      (commutator F χ C e A v c hc (family.cutoff (ε n)) u)))
    (houterbound : (∫ X, sourceIntegrand O α τ
      (commutator F χ C e A v c hc (family.cutoff (R / 2)) u) X) ≤ B)
    (herror : Tendsto (fun n => ∫ X, sourceIntegrand O α τ
      (commutator F χ C e A v c hc (family.cutoff (ε n)) u) X) atTop (𝓝 0)) :
    (∫⁻ X in Metric.ball O (R / 4), ENNReal.ofReal
      (UniqueContinuation.radialMassIntegrand (fun X => dist X O)
        (PauliReference.wave u) α τ X)) ≤ ENNReal.ofReal (2 * K * B) := by
  let a := family.cutoff (R / 2)
  let b := fun n => family.cutoff (ε n)
  let w := fun X : Configuration N =>
    Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist X O))) * dist X O ^ 2
  let z := fun n => PauliReference.wave (localize (twiceSub a (b n)).scalar u)
  let source := fun η => commutator F χ C e A v c hc η u
  have hpoint : ∀ᵐ X ∂volume.restrict (Metric.ball O (R / 4)), ∀ᶠ n in atTop,
      z n X = PauliReference.wave u X := by
    filter_upwards [scalar_buffered_cutoff_eventually_identity (PauliReference.wave u)
      hR (by linarith : R / 4 ≤ R / 2) a b ε hε hεlim
      (family.weight (R / 2) (half_pos hR)) (fun n => family.weight (ε n) (hε n))] with X hX
    filter_upwards [hX] with n hn
    exact (congrArg (fun f : PauliReference.Wave N => f X)
      (PauliInfiniteOrder.wave_localize (twiceSub a (b n)).scalar u)).trans hn
  apply CarlemanCutoffPassage.remove_inner_source (ν := volume)
    (F := fun n X => ENNReal.ofReal
      (UniqueContinuation.radialMassIntegrand (fun X => dist X O) (z n) α τ X))
    (w := w) (outer := source a) (inner := fun n => source (b n))
    (total := fun n => source (twiceSub a (b n))) hK
    (Filter.Eventually.of_forall fun X => by dsimp [w]; positivity)
  · intro n
    exact (UniqueContinuation.radialMassIntegrand_measurable
      (Lp.stronglyMeasurable (z n)).norm.measurable
      (continuous_id.dist continuous_const).measurable α τ).ennreal_ofReal.aemeasurable
  · filter_upwards [hpoint] with X hX
    apply tendsto_const_nhds.congr'
    filter_upwards [hX] with n hn
    exact congrArg ENNReal.ofReal
      (congrArg (fun q : Fiber N PhotonFock => τ ^ 3 *
        UniqueContinuation.weightedNormSq
          (fun Y => CarlemanWeights.beta α (-Real.log (dist Y O)) * dist Y O ^ (-2 : ℝ))
          (fun Y => CarlemanWeights.weight α (-Real.log (dist Y O)))
          (fun _ => q) τ X) hn.symm)
  · exact houter
  · exact hinner
  · intro n
    have hw : Measurable w := by unfold w CarlemanWeights.weight; fun_prop
    exact (hw.mul ((Lp.stronglyMeasurable (source (twiceSub a (b n)))).norm.measurable.pow_const 2)).aestronglyMeasurable
  · intro n
    have heq := commutator_sub F χ C e A v c hc a (b n) u
    filter_upwards [Lp.coeFn_sub (source a) (source (b n))] with X hX
    exact (congrArg (fun q : PauliReference.Wave N => q X) heq).trans hX
  · intro n
    have h := hCarleman u heigen family (ε n) (hε n) (hεR n) τ hτ
    have hl := lintegral_mono'
      (μ := volume.restrict (Metric.ball O (R / 4)))
      (ν := volume.restrict (Metric.ball O R)) (f := fun X => ENNReal.ofReal
      (UniqueContinuation.radialMassIntegrand (fun X => dist X O) (z n) α τ X))
      (Measure.restrict_mono (Metric.ball_subset_ball (by linarith : R / 4 ≤ R)) le_rfl) (le_refl _)
    exact (hl.trans h).trans (mul_le_mul' le_rfl
      (lintegral_mono' Measure.restrict_le_self (le_refl _)))
  · exact houterbound
  · exact herror

end PfHk.PauliOperatorCarleman
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
