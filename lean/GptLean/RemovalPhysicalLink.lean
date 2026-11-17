import GptLean.RemovalPhysicalChannel
import GptLean.RemovalSourceLink

/-! The actual cluster construction supplies the source link used by exact
constraint assembly. No phase or target-domain property remains an input. -/

noncomputable section

namespace GptLean.RemovalEnergy

open MeasureTheory Filter Repair SymmetricLift RemovalGeometry RemovalState
open scoped ContDiff ENNReal

variable {Q H F T ι : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {N : ℕ}

def cluster_physicalSourceLink
    (S : ConditionedSource μ (volume : Measure (Configuration N)) (Fin N × Fin 3) H F)
    (B₀ : TensorBackground SixTag) (B₁ : TensorMultilinearData B₀)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B₀ N).target) (index : ι ↪ ℕ)
    (Rrad : H →ₗ.[ℂ] H) (A : (Fin N × Fin 3) → Configuration N → H →ₗ.[ℂ] H)
    (B : Configuration N → H →ₗ.[ℂ] F)
    (R₁ : Gaussian.RankOneData (Lp H 2 (volume : Measure (Configuration N))) T)
    (Tr : PositiveTraceData T) (E : PositiveForm Tr)
    {R e : ℝ} (CZ k acut bcut : ℝ) (hR : 0 < R) (he : 0 ≤ e)
    (c : ℕ → Fin N → ClusterSpace) (a : Q → ClusterSpace → ClusterSpace)
    (P : S.PFData Rrad A B e (physicalSoftField a))
    (hform : HasPFFormEvaluation Rrad A B e (fun v => E.expectation (R₁.rankOne v)))
    (ha : StronglyMeasurable (Function.uncurry a)) (hd : ∀ q, ContDiff ℝ ∞ (a q))
    (hda : ∀ j : Fin 3, StronglyMeasurable (fun qx : Q × ClusterSpace =>
      fderiv ℝ (a qx.1) qx.2 (EuclideanSpace.single j 1)))
    (Z : ℕ → Q → ℝ) (hZmeas : ∀ n, Measurable (Z n)) (hZ : ∀ n q, 0 ≤ Z n q)
    (hbound : ∀ n q s, ∀ y ∈ Metric.ball (physicalClusterCentre (c n) R s) (clusterRadius N R),
      ‖fderiv ℝ (a q) y‖ ≤ Z n q)
    (hsupport : ∀ n, ∀ᵐ qx ∂μ.prod volume, S.source n qx ≠ 0 →
      ∀ i : Fin N, ∃ j, dist (particle qx.2 i) (c n j) ≤ 4 * R)
    (hsecond : ∀ n, Integrable
      (fun q => sourceMass (ν := volume) (S.source n) q * Z n q ^ 2) μ)
    (hsecond_bound : ∀ n, (∫ q, sourceMass (ν := volume) (S.source n) q * Z n q ^ 2 ∂μ) ≤
      CZ * k ^ 2 * (acut ^ 2 * S.soft n + bcut ^ 2 * ‖S.source n‖ ^ 2))
    (hpositive : R₁.positive ⊆ Tr.positive) (htrace : R₁.trace = Tr.trace) :
    PhysicalSourceLink S
      (cluster_physicalChannelData S B₀ B₁ basis index Rrad A B R₁ Tr E CZ k acut bcut
        hR he c a P hform ha hd hda Z hZmeas hZ hbound hsupport hsecond hsecond_bound
        hpositive htrace) (physicalSoftField a) := by
  refine {
    phase := fun n q => configurationClusterPhase (c n) R e (a q)
    phase_measurable := ?_
    phase_smooth := fun n q => configurationClusterPhase_contDiff (c n) R e (a q)
    phase_bound := ?_
    source := rfl
    covariant := rfl
    input := rfl
    soft := rfl
    weak := ?_
    cancellation := ?_
  }
  · intro n
    have hm := configurationClusterPhase_jointly_stronglyMeasurable (c n) R e ha
    exact ((Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const)).comp_stronglyMeasurable hm)
  · intro n q
    obtain ⟨M, _, hM⟩ := configurationClusterPhase_exists_derivative_bound (c n) hR e (a q)
    exact ⟨M, hM⟩
  · intro n
    exact Filter.Eventually.of_forall
      (clusterChannel_properties B₀ B₁ basis index (c n) hR he μ
        (hZmeas n) (hZ n) ha hd hda (hbound n)).2.2.1
  · intro n j
    filter_upwards [hsupport n] with qx hx
    intro hn
    exact configurationClusterPhase_cancellation (c n) hR e (a qx.1) qx.2 j (hx hn j.1)

end GptLean.RemovalEnergy
