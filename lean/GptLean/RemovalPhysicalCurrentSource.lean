import GptLean.RemovalPhysicalCurrent
import GptLean.RemovalPhysicalSource

/-!
The current and energy evaluations share one physical conditioned source.
The same phase and residual cancellation produce the hard covariant
derivative in both formulas, and the same weak lift supplies each repair
coordinate. No output-specific current evaluation is a hypothesis.
-/

noncomputable section

namespace GptLean.RemovalPhysicalCurrent

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open MeasureTheory MeasureTheory.Measure Filter Repair SymmetricLift RemovalState RemovalEnergy
open scoped ContDiff Topology ENNReal

variable {I V H T Test : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {Tr : PositiveTraceData T} {E : PositiveForm Tr}

theorem phase_canonical_current_coordinate
    (rankOne : Gaussian.RankOneData (Lp H 2 (volume : Measure (EuclideanSpace ℝ I))) T)
    (radiation : H →ₗ.[ℂ] H)
    (field : I → EuclideanSpace ℝ I → H →ₗ.[ℂ] H) (e : ℝ)
    (current : Test → FormObservable E) (weight : Test → EuclideanSpace ℝ I → ℝ)
    (direction : Test → I)
    (hcanonical : CanonicalCurrent rankOne radiation field e current weight direction)
    (basis : HilbertBasis ℕ ℂ V)
    {z : EuclideanSpace ℝ I → V} {dz : I → EuclideanSpace ℝ I → V}
    {ψ rψ : EuclideanSpace ℝ I → H} {dψ aψ u : I → EuclideanSpace ℝ I → H}
    {φ : EuclideanSpace ℝ I → ℝ} {s a : I → EuclideanSpace ℝ I → ℝ}
    (hz : HasWeakH1Local z dz) (hunit : ∀ᵐ x ∂volume, ‖z x‖ ≤ 1)
    (hψ : MemLp ψ 2 volume) (hweak : HasWeakH1Local ψ dψ)
    (hdψ : ∀ j, MemLp (dψ j) 2 volume) (hrψ : MemLp rψ 2 volume)
    (hrad : ∀ᵐ x ∂volume, (ψ x, rψ x) ∈ radiation.graph)
    (haψ : ∀ j, MemLp (aψ j) 2 volume)
    (hfield : ∀ j, ∀ᵐ x ∂volume, (ψ x, aψ j x) ∈ (field j x).graph)
    (hφ : ContDiff ℝ ∞ φ) (P : ℝ)
    (hP : ∀ j x, |fderiv ℝ φ x (EuclideanSpace.single j 1)| ≤ P)
    (hcov : ∀ j, ∀ᵐ x ∂volume,
      u j x = -Complex.I • dψ j x - (e : ℂ) • aψ j x - ((e * a j x : ℝ) : ℂ) • ψ x)
    (hcancel : ∀ j, ∀ᵐ x ∂volume, ψ x ≠ 0 →
      fderiv ℝ φ x (EuclideanSpace.single j 1) + s j x = -e * a j x)
    (M : ℝ) (hmetric : ∀ᵐ x ∂volume, ∑ j, ‖dz j x‖ ^ 2 ≤ M) (j : ℕ) (t : Test) :
    ∃ hout : MemLp (channelValue basis z (fun x => gaugePhase φ x • ψ x) j) 2 volume,
      Tendsto (fun n => (current t).approximation n
        (rankOne.rankOne (hout.toLp (channelValue basis z (fun x => gaugePhase φ x • ψ x) j))))
        atTop (𝓝 ((∫ x, inner ℂ (channelValue basis z (fun y => gaugePhase φ y • ψ y) j x)
          (channelDerivative basis z (fun y => (weight t y : ℂ) • dz (direction t) y)
            (fun y => (weight t y : ℂ) • (gaugePhase φ y •
              (u (direction t) y - (s (direction t) y : ℂ) • ψ y)))
            (fun y => gaugePhase φ y • ψ y) j x) ∂volume).re)) := by
  let w := gaugePhase φ
  let dw := fun i x => fderiv ℝ w x (EuclideanSpace.single i 1)
  have hw : HasWeakH1Local w dw := weakH1Local_of_contDiff (gaugePhase_contDiff hφ)
  have hb : ∀ᵐ x ∂volume, ‖w x‖ ≤ 1 := Eventually.of_forall fun x => (gaugePhase_norm φ x).le
  have htop : MemLp w ∞ volume :=
    memLp_top_of_bound (gaugePhase_contDiff hφ).continuous.aestronglyMeasurable 1 hb
  obtain ⟨hp, hwp, hdp, hrp, hrg⟩ := pf_reference_product_of_weighted radiation hw hb
    hψ hweak hdψ hrψ hrad (phase_weight_memLp hφ hψ P hP)
  have hap (i : I) : MemLp (fun x => w x • aψ i x) 2 volume := (haψ i).smul htop
  have hag (i : I) : ∀ᵐ x ∂volume, (w x • ψ x, w x • aψ i x) ∈ (field i x).graph :=
    (hfield i).mono (fun x hx => (field i x).graph.smul_mem (w x) hx)
  have href : InPFReferenceDomain radiation (fun x => w x • ψ x) :=
    ⟨hp, _, _, hwp, hdp, hrp, hrg⟩
  have hwz := weighted_lift_integrable_of_metric_bound hz hp M hmetric
  have hout := (coordinate_channel_pf_reference radiation basis hz hunit href hwz j).1
  have hu (i : I) : ∀ᵐ x ∂volume,
      w x • (u i x - (s i x : ℂ) • ψ x) =
        -Complex.I • (w x • dψ i x + dw i x • ψ x) - (e : ℂ) • (w x • aψ i x) := by
    filter_upwards [hcov i, hcancel i] with x hx hc
    have he := (phase_covariant_cancellation (w x)
      (fderiv ℝ φ x (EuclideanSpace.single i 1)) (s i x) (a i x) e
      (ψ x) (dψ i x) (aψ i x) (u i x) hx hc).symm
    simpa only [dw, w, gaugePhase_fderiv (hφ.differentiable (by simp))] using he
  refine ⟨hout, ?_⟩
  exact canonical_current_coordinate rankOne radiation field e current weight direction hcanonical
    basis hz hunit hp hwp hdp hrp hrg hwz hap hag hu j (hout.toLp _) hout.coeFn_toLp t

end GptLean.RemovalPhysicalCurrent

namespace GptLean.RemovalEnergy.ConditionedSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open MeasureTheory MeasureTheory.Measure Filter Repair SymmetricLift RemovalState RemovalPhysicalCurrent
open scoped ContDiff Topology

variable {Q I H F T V Test : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The same source PFData that gives the channel energy gives its current
limits for every bounded spatial test and direction. -/
theorem PFData.current_rankOne
    {S : ConditionedSource μ (volume : Measure (SourceSpace I)) I H F}
    {R : H →ₗ.[ℂ] H} {A : I → SourceSpace I → H →ₗ.[ℂ] H}
    {B : SourceSpace I → H →ₗ.[ℂ] F} {e : ℝ}
    {softField : ℕ → I → Q × SourceSpace I → ℝ}
    (P : S.PFData R A B e softField)
    (R₁ : Gaussian.RankOneData (Lp H 2 (volume : Measure (SourceSpace I))) T)
    {Tr : PositiveTraceData T} {E : PositiveForm Tr}
    (current : Test → FormObservable E) (weight : Test → SourceSpace I → ℝ) (direction : Test → I)
    (hcanonical : CanonicalCurrent R₁ R A e current weight direction)
    (basis : HilbertBasis ℕ ℂ V)
    (z : ℕ → Q × SourceSpace I → V) (dz : ℕ → I → Q × SourceSpace I → V)
    (φ : ℕ → Q → SourceSpace I → ℝ) (s : ℕ → I → Q × SourceSpace I → ℝ)
    (hz : ∀ n, ∀ᵐ q ∂μ, HasWeakH1Local (fun x => z n (q, x))
      (fun j x => dz n j (q, x)))
    (hunit : ∀ n, ∀ᵐ qx ∂μ.prod volume, ‖z n qx‖ ≤ 1)
    (hφ : ∀ n q, ContDiff ℝ ∞ (φ n q))
    (hφbound : ∀ n q, ∃ C : ℝ, ∀ j x, |fderiv ℝ (φ n q) x (EuclideanSpace.single j 1)| ≤ C)
    (hcancel : ∀ n j, ∀ᵐ qx ∂μ.prod volume, S.source n qx ≠ 0 →
      fderiv ℝ (φ n qx.1) qx.2 (EuclideanSpace.single j 1) + s n j qx =
        -e * softField n j qx)
    (M : ℕ → Q → ℝ)
    (hmetric : ∀ n, ∀ᵐ qx ∂μ.prod volume, ∑ j, ‖dz n j qx‖ ^ 2 ≤ M n qx.1) :
    ∀ t n j, ∀ᵐ q ∂μ,
      Tendsto (fun m => (current t).approximation m
        (R₁.rankOne (channelSection (ν := volume) basis (z n)
          (S.phasedSource (fun n qx => gaugePhase (φ n qx.1) qx.2) n) j q))) atTop
        (𝓝 ((∫ x, inner ℂ
          (channelValue basis (fun y => z n (q, y))
            (fun y => S.phasedSource (fun n qx => gaugePhase (φ n qx.1) qx.2) n (q, y)) j x)
          (channelDerivative basis (fun y => z n (q, y))
            (fun y => (weight t y : ℂ) • dz n (direction t) (q, y))
            (fun y => (weight t y : ℂ) •
              S.phasedHardDerivative (fun n qx => gaugePhase (φ n qx.1) qx.2) s n (direction t) (q, y))
            (fun y => S.phasedSource (fun n qx => gaugePhase (φ n qx.1) qx.2) n (q, y)) j x)
          ∂volume).re)) := by
  intro t n j
  filter_upwards [hz n, ae_ae_of_ae_prod (hunit n), P.weak n,
    lp_sections_memLp (S.source n), lp_sections_memLp (P.radiation n),
    ae_all_iff.mpr (fun l => lp_sections_memLp (P.derivative n l)),
    ae_all_iff.mpr (fun l => lp_sections_memLp (P.hardField n l)),
    ae_ae_of_ae_prod (P.radiation_graph n),
    ae_all_iff.mpr (fun l => ae_ae_of_ae_prod (P.hard_graph n l)),
    ae_all_iff.mpr (fun l => ae_ae_of_ae_prod (P.covariant_eq n l)),
    ae_all_iff.mpr (fun l => ae_ae_of_ae_prod (hcancel n l)), ae_ae_of_ae_prod (hmetric n)]
    with q hzq hunitq hweakq hψq hrq hdq haq hrg hag hcovq hcancelq hm
  obtain ⟨C, hC⟩ := hφbound n q
  obtain ⟨hout, hc⟩ := phase_canonical_current_coordinate R₁ R A e current weight direction hcanonical
    basis hzq hunitq hψq hweakq hdq hrq hrg haq hag (hφ n q) C hC hcovq hcancelq (M n q) hm j t
  rw [channelSection, toL2Section_eq
    (f := fun q x => coordinate basis (z n (q, x)) j •
      S.phasedSource (fun n qx => gaugePhase (φ n qx.1) qx.2) n (q, x)) (q := q) hout]
  exact hc

end GptLean.RemovalEnergy.ConditionedSource
