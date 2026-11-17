import PfHk.WeylGraphC1Calculus
import GptLean.PhysicalWeightedRadiation

/-! An actual free Sobolev-radiation reference vector obtained by Weyl
multiplication of an ordinary smooth operator-core representative.
This construction is universal in the displacement labels. -/

noncomputable section
namespace PfHk.WeylCoreReference

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
  GptLean.PhysicalPFReference GptLean.Representability PfHk.PhysicalOperatorDomain
  PfHk.WeylGraphC1Calculus
open scoped ENNReal Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 250000
attribute [local irreducible] radiationGraphInclusion fullRadiationInclusion fullRootProjection

private theorem norm_product_integrable {E H K : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {y : E → K} {u : E → H} (hy : Continuous y) (hu : Continuous u)
    (hs : HasCompactSupport u) : Integrable (fun x => ‖y x‖^2 * ‖u x‖^2) μ := by
  have hs' : HasCompactSupport (fun x => ‖u x‖^2) := by
    simpa only [Function.comp_def] using
      hs.comp_left (g := fun z : H => ‖z‖^2) (by simp)
  apply ((hy.norm.pow 2).mul (hu.norm.pow 2)).integrable_of_hasCompactSupport
  exact hs'.mul_left

variable {I : Type} [Fintype I] [DecidableEq I]
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (h : Position I → WeightedPhotonKernel) (hc : ContDiff ℝ (1 : ℕ∞) h)
  (y : Position I → Lp ℂ 2 photonMeasure) (hyc : Continuous y)
  (hy : ∀ x, ∀ᵐ p ∂photonMeasure, y x p = (Real.sqrt ‖p.1‖ : ℂ) * (h x).val.1 p)
  {s : Set (Position I)} (a : SmoothCore s)

def graph (x : Position I) : RadiationGraphSpace :=
  weylWeightedGraph W (h x).val.1 (y x) (hy x) (a.rootWave x)

theorem graph_inclusion (x : Position I) :
    radiationGraphInclusion (graph W h y hy a x) = W.weyl (h x).val.1 (fullRadiationInclusion (a.representative x)) := by
  unfold graph
  rw [weylWeightedGraph_inclusion]
  unfold SmoothCore.rootWave fullRadiationInclusion
  rfl

include hc hyc in
theorem graph_memLp : MemLp (graph W h y hy a) 2 volume := by
  have hf : Continuous (fun x => (h x).val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp hc.continuous)
  have hpol : Integrable (fun x => ‖y x‖ ^ 2 * ‖radiationGraphInclusion (a.rootWave x)‖ ^ 2) := by
    exact norm_product_integrable hyc a.value_smooth.continuous a.value_compact
  exact weylWeightedGraph_memLp W (fun x => (h x).val.1) y hy a.rootWave
    hf.aestronglyMeasurable a.rootWave_memLp hpol

include B hc in
theorem value_contDiff : ContDiff ℝ (1 : ℕ∞) (C1ReferenceCore.valueFunction (graph W h y hy a)) := by
  have hf : ContDiff ℝ (1 : ℕ∞) (fun x => (h x).val.1) :=
    (((ContinuousLinearMap.fst ℂ _ _).comp weightedKernelSubspace.subtypeL).restrictScalars ℝ).contDiff.comp hc
  have hu := a.value_smooth
  have hfinite : ∀ x, FiniteNumberSupport photonMeasure a.photonCutoff
      (C1ReferenceCore.valueFunction a.rootWave x) := by
    intro x
    convert! a.photonFinite x using 1
    unfold C1ReferenceCore.valueFunction SmoothCore.rootWave fullRadiationInclusion
    rfl
  have hh := B.ambient_c1 (Position I) _ _ a.photonCutoff hf hu hfinite
  have he : C1ReferenceCore.valueFunction (graph W h y hy a) =
      fun x => W.weyl (h x).val.1 (C1ReferenceCore.valueFunction a.rootWave x) :=
    funext fun x => weylWeightedGraph_inclusion W (h x).val.1 (y x) (hy x) (a.rootWave x)
  rw [he]
  exact hh

theorem value_compact : HasCompactSupport (C1ReferenceCore.valueFunction (graph W h y hy a)) := by
  apply a.value_compact.mono
  intro x hx
  change C1ReferenceCore.valueFunction a.rootWave x ≠ 0
  intro hz
  apply hx
  change radiationGraphInclusion (a.rootWave x) = 0 at hz
  unfold C1ReferenceCore.valueFunction graph
  rw [weylWeightedGraph_inclusion, hz, map_zero]

def reference : Reference I (fun _ => 0) :=
  C1ReferenceCore.reference (graph W h y hy a) (graph_memLp W h hc y hyc hy a)
    (value_contDiff W B h hc y hy a) (value_compact W h y hy a)

theorem reference_value_ae :
    inclusion I (fun _ => 0) (reference W B h hc y hyc hy a) =ᵐ[volume]
      fun x => W.weyl (h x).val.1 (fullRadiationInclusion (a.representative x)) := by
  have he := C1ReferenceCore.reference_value (graph W h y hy a) (graph_memLp W h hc y hyc hy a)
    (value_contDiff W B h hc y hy a) (value_compact W h y hy a)
  have ha := (C1ReferenceCore.value_memLp (graph W h y hy a) (graph_memLp W h hc y hyc hy a)).coeFn_toLp
  exact ((Filter.EventuallyEq.of_eq (congrArg (fun v : WaveSpace I => ⇑v) he)).trans ha).trans
    (Filter.EventuallyEq.of_eq (funext (graph_inclusion W h y hy a)))

theorem reference_graph_ae :
    radiationSource I (fun _ => 0) (reference W B h hc y hyc hy a) =ᵐ[volume]
      graph W h y hy a := by
  have he := C1ReferenceCore.reference_value (graph W h y hy a) (graph_memLp W h hc y hyc hy a)
    (value_contDiff W B h hc y hy a) (value_compact W h y hy a)
  have ha := (C1ReferenceCore.value_memLp (graph W h y hy a) (graph_memLp W h hc y hyc hy a)).coeFn_toLp
  have hv := (Filter.EventuallyEq.of_eq (congrArg (fun v : WaveSpace I => ⇑v) he)).trans ha
  have hm := radiation_matches I (fun _ => 0) (reference W B h hc y hyc hy a)
  filter_upwards [hv, radiationGraphInclusion.coeFn_compLpL
    (radiationSource I (fun _ => 0) (reference W B h hc y hyc hy a))] with x hx hq
  apply radiationGraphInclusion_injective_weyl
  exact hq.symm.trans ((congrArg (fun v : WaveSpace I => v x) hm).trans hx)

theorem reference_ordinary_ae (j : I) :
    ordinary I (fun _ => 0) j (reference W B h hc y hyc hy a) =ᵐ[volume]
      fun x => fderiv ℝ (fun z => W.weyl (h z).val.1
        (fullRadiationInclusion (a.representative z))) x (EuclideanSpace.single j 1) := by
  have he := C1ReferenceCore.reference_ordinary (graph W h y hy a) (graph_memLp W h hc y hyc hy a)
    (value_contDiff W B h hc y hy a) (value_compact W h y hy a) j
  have ha := (C1ReferenceCore.derivative_memLp (graph W h y hy a)
    (value_contDiff W B h hc y hy a) (value_compact W h y hy a) j).coeFn_toLp
  have hf : C1ReferenceCore.valueFunction (graph W h y hy a) =
      fun z => W.weyl (h z).val.1 (fullRadiationInclusion (a.representative z)) :=
    funext (graph_inclusion W h y hy a)
  apply ((Filter.EventuallyEq.of_eq (congrArg (fun v : WaveSpace I => ⇑v) he)).trans ha).trans
  apply Filter.EventuallyEq.of_eq
  funext x
  unfold C1ReferenceCore.derivativeFunction
  rw [hf]

/-- Compact support strictly inside the open test region, expressed using
the actual L2 inclusion and hence independent of representative choices. -/
def CompactlySupportedIn (s : Set (Position I)) (v : Reference I (fun _ => 0)) : Prop :=
  ∃ K : Set (Position I), IsCompact K ∧ K ⊆ s ∧
    ∀ᵐ x ∂volume, x ∉ K → inclusion I (fun _ => 0) v x = 0

/-- The standard Weyl form-core density theorem. Its topology is exactly
the norm of the actual free Reference graph, which includes ordinary H1
and the radiation form graph. Its labels, regions and test vectors are
arbitrary. No physical coefficient, polar equation or estimate occurs in
this retained operator-theory input. -/
structure StandardWeylFormCoreDensity (W : ConcreteWeylLaw photonMeasure)
    (B : StandardWeylGraphC1 W) : Prop where
  approximate : ∀ (I : Type) [Fintype I] [DecidableEq I]
    (h : Position I → WeightedPhotonKernel) (hc : ContDiff ℝ (1 : ℕ∞) h)
    (y : Position I → Lp ℂ 2 photonMeasure) (hyc : Continuous y)
    (hy : ∀ x, ∀ᵐ p ∂photonMeasure, y x p = (Real.sqrt ‖p.1‖ : ℂ) * (h x).val.1 p)
    (s : Set (Position I)), IsOpen s → ∀ v : Reference I (fun _ => 0),
    CompactlySupportedIn s v → ∃ a : ℕ → SmoothCore s,
      Filter.Tendsto (fun n => reference W B h hc y hyc hy (a n)) Filter.atTop (𝓝 v)

end PfHk.WeylCoreReference
