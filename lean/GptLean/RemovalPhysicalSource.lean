import GptLean.Repair.ScalarFormOperations
import GptLean.Repair.ChannelFormEvaluation
import GptLean.RemovalConditioned

/-!
The physical derivative of the phased source is the derivative used by
the removal channel. Only the original source has domain hypotheses.
The phase product rule, radiation and field graphs, channel domain and
rank-one form value are all derived for the actual constructed vectors.
-/

noncomputable section

namespace GptLean.RemovalEnergy

open MeasureTheory Filter Repair SymmetricLift
open scoped ContDiff ENNReal

variable {I V H F : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem phase_covariant_cancellation (w : ℂ) (p s a e : ℝ)
    (ψ dψ aψ u : H)
    (hu : u = -Complex.I • dψ - (e : ℂ) • aψ - ((e * a : ℝ) : ℂ) • ψ)
    (hc : ψ ≠ 0 → p + s = -e * a) :
    -Complex.I • (w • dψ + (w * (p : ℂ) * Complex.I) • ψ) -
      (e : ℂ) • (w • aψ) = w • (u - (s : ℂ) • ψ) := by
  rw [hu]
  by_cases hz : ψ = 0
  · simp only [hz, smul_zero, add_zero, sub_zero, smul_sub, smul_smul]
    module
  · have hpc : (p : ℂ) = -((e * a : ℝ) : ℂ) - (s : ℂ) := by
      have h := congrArg (fun x : ℝ => (x : ℂ)) (hc hz)
      push_cast at h ⊢
      linear_combination h
    simp only [smul_add, smul_sub, smul_smul, neg_mul, mul_neg]
    rw [show -(Complex.I * (w * (p : ℂ) * Complex.I)) = w * (p : ℂ) by
      calc
        _ = -(w * (p : ℂ) * (Complex.I * Complex.I)) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring]
    rw [hpc]
    module

/-- A smooth phase with bounded gradient has the weighted derivative
needed by the source-domain product rule, for every finite-energy source. -/
theorem phase_weight_memLp
    {φ : EuclideanSpace ℝ I → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {ψ : EuclideanSpace ℝ I → H} (hψ : MemLp ψ 2 volume)
    (P : ℝ) (hP : ∀ i x, |fderiv ℝ φ x (EuclideanSpace.single i 1)| ≤ P) (i : I) :
    MemLp (fun x => fderiv ℝ (gaugePhase φ) x (EuclideanSpace.single i 1) • ψ x)
      2 volume := by
  have hm : AEStronglyMeasurable
      (fun x => fderiv ℝ (gaugePhase φ) x (EuclideanSpace.single i 1)) volume :=
    (((gaugePhase_contDiff hφ).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable
  have hb : ∀ᵐ x ∂volume,
      ‖fderiv ℝ (gaugePhase φ) x (EuclideanSpace.single i 1)‖ ≤ P := by
    filter_upwards with x
    rw [gaugePhase_fderiv (hφ.differentiable (by simp))]
    simpa only [norm_mul, gaugePhase_norm, Complex.norm_real, Complex.norm_I,
      one_mul, mul_one, Real.norm_eq_abs] using hP i x
  exact hψ.smul (memLp_top_of_bound hm P hb)

/-- Physical form evaluation of the actual phase and repair channel.
The cancellation condition is required only where the source is nonzero,
as follows from localization and the cluster plateau identity. -/
theorem phase_coordinate_channel_form_evaluation
    (R : H →ₗ.[ℂ] H)
    (A : I → EuclideanSpace ℝ I → H →ₗ.[ℂ] H)
    (B : EuclideanSpace ℝ I → H →ₗ.[ℂ] F)
    (e : ℝ) (form : Lp H 2 (volume : Measure (EuclideanSpace ℝ I)) → ℝ≥0∞)
    (hform : HasPFFormEvaluation R A B e form)
    (basis : HilbertBasis ℕ ℂ V)
    {z : EuclideanSpace ℝ I → V} {dz : I → EuclideanSpace ℝ I → V}
    {ψ rψ : EuclideanSpace ℝ I → H}
    {dψ aψ u : I → EuclideanSpace ℝ I → H}
    {rest : EuclideanSpace ℝ I → F}
    {φ : EuclideanSpace ℝ I → ℝ} {s a : I → EuclideanSpace ℝ I → ℝ}
    (hz : HasWeakH1Local z dz) (hunit : ∀ᵐ x ∂volume, ‖z x‖ ≤ 1)
    (hψ : MemLp ψ 2 volume) (hweak : HasWeakH1Local ψ dψ)
    (hdψ : ∀ i, MemLp (dψ i) 2 volume) (hrψ : MemLp rψ 2 volume)
    (hrad : ∀ᵐ x ∂volume, (ψ x, rψ x) ∈ R.graph)
    (haψ : ∀ i, MemLp (aψ i) 2 volume)
    (hfield : ∀ i, ∀ᵐ x ∂volume, (ψ x, aψ i x) ∈ (A i x).graph)
    (hrest : MemLp rest 2 volume)
    (hrestgraph : ∀ᵐ x ∂volume, (ψ x, rest x) ∈ (B x).graph)
    (hφ : ContDiff ℝ ∞ φ) (P : ℝ)
    (hP : ∀ i x, |fderiv ℝ φ x (EuclideanSpace.single i 1)| ≤ P)
    (hcov : ∀ i, ∀ᵐ x ∂volume,
      u i x = -Complex.I • dψ i x - (e : ℂ) • aψ i x - ((e * a i x : ℝ) : ℂ) • ψ x)
    (hcancel : ∀ i, ∀ᵐ x ∂volume, ψ x ≠ 0 →
      fderiv ℝ φ x (EuclideanSpace.single i 1) + s i x = -e * a i x)
    (M : ℝ) (hmetric : ∀ᵐ x ∂volume, ∑ i, ‖dz i x‖ ^ 2 ≤ M)
    (j : ℕ) :
    ∃ hout : MemLp (channelValue basis z (fun x => gaugePhase φ x • ψ x) j) 2 volume,
      InPFReferenceDomain R (channelValue basis z (fun x => gaugePhase φ x • ψ x) j) ∧
      form (hout.toLp (channelValue basis z (fun x => gaugePhase φ x • ψ x) j)) =
        ENNReal.ofReal ((∫ x, 1 / 2 * ∑ i,
          ‖channelDerivative basis z (dz i)
            (fun y => gaugePhase φ y • (u i y - (s i y : ℂ) • ψ y))
            (fun y => gaugePhase φ y • ψ y) j x‖ ^ 2) +
          (∫ x, ‖coordinate basis (z x) j • (gaugePhase φ x • rest x)‖ ^ 2)) := by
  let w := gaugePhase φ
  let dw := fun i x => fderiv ℝ w x (EuclideanSpace.single i 1)
  have hw : HasWeakH1Local w dw := weakH1Local_of_contDiff (gaugePhase_contDiff hφ)
  have hb : ∀ᵐ x ∂volume, ‖w x‖ ≤ 1 := Eventually.of_forall fun x => (gaugePhase_norm φ x).le
  have htop : MemLp w ∞ volume :=
    memLp_top_of_bound (gaugePhase_contDiff hφ).continuous.aestronglyMeasurable 1 hb
  obtain ⟨hp, hwp, hdp, hrp, hrg⟩ := pf_reference_product_of_weighted R hw hb
    hψ hweak hdψ hrψ hrad (phase_weight_memLp hφ hψ P hP)
  have hap (i : I) : MemLp (fun x => w x • aψ i x) 2 volume := (haψ i).smul htop
  have hag (i : I) : ∀ᵐ x ∂volume, (w x • ψ x, w x • aψ i x) ∈ (A i x).graph :=
    (hfield i).mono (fun x hx => (A i x).graph.smul_mem (w x) hx)
  have hr : MemLp (fun x => w x • rest x) 2 volume := hrest.smul htop
  have hrg' : ∀ᵐ x ∂volume, (w x • ψ x, w x • rest x) ∈ (B x).graph :=
    hrestgraph.mono (fun x hx => (B x).graph.smul_mem (w x) hx)
  have hwz := weighted_lift_integrable_of_metric_bound hz hp M hmetric
  obtain ⟨hout, hdomain, hvalue⟩ := coordinate_channel_form_evaluation R A B e form hform basis
    hz hunit hp hwp hdp hrp hrg hap hag hr hrg' hwz j
  refine ⟨hout, hdomain, hvalue.trans ?_⟩
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hcov, ae_all_iff.mpr hcancel] with x hx hc
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hid := phase_covariant_cancellation (w x)
    (fderiv ℝ φ x (EuclideanSpace.single i 1)) (s i x) (a i x) e
    (ψ x) (dψ i x) (aψ i x) (u i x) (hx i) (hc i)
  simp only [dw, w, gaugePhase_fderiv (hφ.differentiable (by simp))] at *
  simp only [channelDerivative, hid]

end GptLean.RemovalEnergy

namespace GptLean.RemovalEnergy

open MeasureTheory MeasureTheory.Measure Filter Repair SymmetricLift RemovalState
open scoped ContDiff ENNReal

variable {Q I H F T V : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

abbrev SourceSpace (I : Type*) [Fintype I] := EuclideanSpace ℝ I

namespace ConditionedSource

/-- Source-only WIS graph data. Every field is an actual L² vector or a
weak/partial-operator identity for the original localized source. This
contains no phase, lift, target domain, target form, or removal estimate. -/
structure PFData (S : ConditionedSource μ (volume : Measure (SourceSpace I)) I H F)
    (R : H →ₗ.[ℂ] H) (A : I → SourceSpace I → H →ₗ.[ℂ] H)
    (B : SourceSpace I → H →ₗ.[ℂ] F) (e : ℝ)
    (softField : ℕ → I → Q × SourceSpace I → ℝ) where
  derivative : ℕ → I → Lp H 2 (μ.prod (volume : Measure (SourceSpace I)))
  radiation : ℕ → Lp H 2 (μ.prod (volume : Measure (SourceSpace I)))
  hardField : ℕ → I → Lp H 2 (μ.prod (volume : Measure (SourceSpace I)))
  weak : ∀ n, ∀ᵐ q ∂μ, HasWeakH1Local (fun x => S.source n (q, x))
    (fun j x => derivative n j (q, x))
  radiation_graph : ∀ n, ∀ᵐ qx ∂μ.prod volume,
    (S.source n qx, radiation n qx) ∈ R.graph
  hard_graph : ∀ n j, ∀ᵐ qx ∂μ.prod volume,
    (S.source n qx, hardField n j qx) ∈ (A j qx.2).graph
  rest_graph : ∀ n, ∀ᵐ qx ∂μ.prod volume,
    (S.source n qx, S.rest n qx) ∈ (B qx.2).graph
  covariant_eq : ∀ n j, ∀ᵐ qx ∂μ.prod volume,
    S.covariant n j qx = -Complex.I • derivative n j qx -
      (e : ℂ) • hardField n j qx - ((e * softField n j qx : ℝ) : ℂ) • S.source n qx

theorem lp_sections_memLp {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (v : Lp K 2 (μ.prod (volume : Measure (SourceSpace I)))) :
    ∀ᵐ q ∂μ, MemLp (fun x => v (q, x)) 2 volume := by
  filter_upwards [(lp_quadratic_integrable v).prod_right_ae] with q hq
  exact (memLp_two_iff_integrable_sq_norm
    ((Lp.stronglyMeasurable v).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hq

/-- The source PF graphs, an actual smooth phase, and a weak repair lift
give the channel's rank-one form identity. The output-domain conclusion
of the preceding theorem is used before identifying the total L² section. -/
theorem PFData.rankOne_form
    {S : ConditionedSource μ (volume : Measure (SourceSpace I)) I H F}
    {R : H →ₗ.[ℂ] H} {A : I → SourceSpace I → H →ₗ.[ℂ] H}
    {B : SourceSpace I → H →ₗ.[ℂ] F} {e : ℝ}
    {softField : ℕ → I → Q × SourceSpace I → ℝ}
    (P : S.PFData R A B e softField)
    (R₁ : Gaussian.RankOneData (Lp H 2 (volume : Measure (SourceSpace I))) T)
    (Tr : PositiveTraceData T) (E : PositiveForm Tr)
    (hform : HasPFFormEvaluation R A B e (fun v => E.expectation (R₁.rankOne v)))
    (basis : HilbertBasis ℕ ℂ V)
    (z : ℕ → Q × SourceSpace I → V) (dz : ℕ → I → Q × SourceSpace I → V)
    (φ : ℕ → Q → SourceSpace I → ℝ) (s : ℕ → I → Q × SourceSpace I → ℝ)
    (hz : ∀ n, ∀ᵐ q ∂μ, HasWeakH1Local (fun x => z n (q, x))
      (fun j x => dz n j (q, x)))
    (hunit : ∀ n, ∀ᵐ qx ∂μ.prod volume, ‖z n qx‖ ≤ 1)
    (hφ : ∀ n q, ContDiff ℝ ∞ (φ n q))
    (hφbound : ∀ n q, ∃ C : ℝ, ∀ j x,
      |fderiv ℝ (φ n q) x (EuclideanSpace.single j 1)| ≤ C)
    (hcancel : ∀ n j, ∀ᵐ qx ∂μ.prod volume, S.source n qx ≠ 0 →
      fderiv ℝ (φ n qx.1) qx.2 (EuclideanSpace.single j 1) + s n j qx =
        -e * softField n j qx)
    (M : ℕ → Q → ℝ)
    (hmetric : ∀ n, ∀ᵐ qx ∂μ.prod volume, ∑ j, ‖dz n j qx‖ ^ 2 ≤ M n qx.1) :
    ∀ n j, ∀ᵐ q ∂μ,
      E.expectation (R₁.rankOne (channelSection (ν := volume) basis (z n)
        (S.phasedSource (fun n qx => gaugePhase (φ n qx.1) qx.2) n) j q)) =
      ENNReal.ofReal ((∫ x, 1 / 2 * ∑ l,
        ‖channelDerivative basis (fun y => z n (q, y)) (fun y => dz n l (q, y))
          (fun y => S.phasedHardDerivative (fun n qx => gaugePhase (φ n qx.1) qx.2) s n l (q, y))
          (fun y => S.phasedSource (fun n qx => gaugePhase (φ n qx.1) qx.2) n (q, y)) j x‖ ^ 2) +
        (∫ x, ‖coordinate basis (z n (q, x)) j •
          S.phasedRest (fun n qx => gaugePhase (φ n qx.1) qx.2) n (q, x)‖ ^ 2)) := by
  intro n j
  filter_upwards [hz n, ae_ae_of_ae_prod (hunit n), P.weak n,
    lp_sections_memLp (S.source n), lp_sections_memLp (P.radiation n),
    lp_sections_memLp (S.rest n),
    ae_all_iff.mpr (fun l => lp_sections_memLp (P.derivative n l)),
    ae_all_iff.mpr (fun l => lp_sections_memLp (P.hardField n l)),
    ae_ae_of_ae_prod (P.radiation_graph n), ae_ae_of_ae_prod (P.rest_graph n),
    ae_all_iff.mpr (fun l => ae_ae_of_ae_prod (P.hard_graph n l)),
    ae_all_iff.mpr (fun l => ae_ae_of_ae_prod (P.covariant_eq n l)),
    ae_all_iff.mpr (fun l => ae_ae_of_ae_prod (hcancel n l)),
    ae_ae_of_ae_prod (hmetric n)]
    with q hzq hunitq hweakq hψq hrq hrestq hdq haq hrg hrestg hag hcovq hcancelq hm
  obtain ⟨C, hC⟩ := hφbound n q
  obtain ⟨hout, _, hv⟩ := phase_coordinate_channel_form_evaluation R A B e _ hform basis
    hzq hunitq hψq hweakq hdq hrq hrg haq hag hrestq hrestg
    (hφ n q) C hC hcovq hcancelq (M n q) hm j
  rw [channelSection, toL2Section_eq
    (f := fun q x => coordinate basis (z n (q, x)) j •
      S.phasedSource (fun n qx => gaugePhase (φ n qx.1) qx.2) n (q, x)) (q := q) hout]
  exact hv

end ConditionedSource
end GptLean.RemovalEnergy
