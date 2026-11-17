import GptLean.Repair.TraceChannel
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-!
Jointly measurable representatives give strongly measurable L² sections.
Applied to the actual coordinate multipliers, this removes a separate
measurability assumption on the repaired L² vectors. The remaining inputs
concern the representatives, their sectionwise mass, and the ordinary
separability of the underlying measure and fibre Hilbert space.
-/

namespace GptLean.Repair

open MeasureTheory Set
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency.types false

private theorem measurable_of_measurable_dist
    {Q E : Type*} [MeasurableSpace Q] [MetricSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {f : Q → E} (hf : ∀ y, Measurable (fun q => dist (f q) y)) :
    Measurable f := by
  apply measurable_of_isOpen
  intro s hs
  let I := {p : E × ℝ // Metric.ball p.1 p.2 ⊆ s}
  let U : I → Set E := fun p => Metric.ball p.val.1 p.val.2
  have hcover : (⋃ p, U p) = s := by
    apply Subset.antisymm
    · exact iUnion_subset fun p => p.property
    · intro x hx
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hs x hx
      exact mem_iUnion.mpr ⟨⟨(x, r), hsub⟩, Metric.mem_ball_self hr⟩
  obtain ⟨C, hC, hU⟩ := TopologicalSpace.isOpen_iUnion_countable U
    (fun _ => Metric.isOpen_ball)
  rw [← hcover, ← hU, preimage_iUnion₂]
  exact MeasurableSet.biUnion hC fun p _ =>
    measurableSet_lt (hf p.val.1) measurable_const

variable {Q X H V T : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure X} [SFinite μ] [IsSeparable μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

/-- Joint measurability and sectionwise square integrability imply strong
measurability of the actual L²-valued map. No integrability over the
parameter space is needed. -/
theorem stronglyMeasurable_toL2_sections {f : Q → X → H}
    (hf : StronglyMeasurable (Function.uncurry f))
    (hLp : ∀ q, MemLp (f q) 2 μ) :
    StronglyMeasurable (fun q => (hLp q).toLp (f q)) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  borelize ↥(Lp H 2 μ)
  apply Measurable.stronglyMeasurable
  apply measurable_of_measurable_dist
  intro g
  have hi : Measurable (fun q => ∫ x, ‖f q x - g x‖ ^ 2 ∂μ) :=
    ((hf.sub ((Lp.stronglyMeasurable g).comp_measurable measurable_snd)).norm.pow 2).integral_prod_right.measurable
  convert hi.sqrt using 1
  ext q
  have hn := toL2_norm_sq ((hLp q).sub (Lp.memLp g))
  rw [MemLp.toLp_sub (hLp q) (Lp.memLp g), Lp.toLp_coeFn g (Lp.memLp g)] at hn
  simp only [Pi.sub_apply] at hn
  rw [dist_eq_norm, ← hn, Real.sqrt_sq_eq_abs, abs_norm]

/-- The L² section is zero at parameters where the source section is not
square integrable. This convention makes the section map total. -/
noncomputable def toL2Section (f : Q → X → H) (q : Q) : Lp H 2 μ := by
  classical
  exact if h : MemLp (f q) 2 μ then h.toLp (f q) else 0

omit [MeasurableSpace Q] [SFinite μ] [IsSeparable μ]
  [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H] in
theorem toL2Section_eq {f : Q → X → H} {q : Q} (h : MemLp (f q) 2 μ) :
    toL2Section (μ := μ) f q = h.toLp (f q) := by
  simp only [toL2Section, dite_eq_left h]

omit [MeasurableSpace Q] [SFinite μ] [IsSeparable μ]
  [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H] in
/-- The total L² section depends only on the almost-everywhere class of
its representative, including at non-square-integrable parameters. -/
theorem toL2Section_congr {f g : Q → X → H} {q : Q}
    (hfg : f q =ᵐ[μ] g q) :
    toL2Section (μ := μ) f q = toL2Section (μ := μ) g q := by
  by_cases hf : MemLp (f q) 2 μ
  · have hg := (memLp_congr_ae hfg).mp hf
    rw [toL2Section_eq hf, toL2Section_eq hg]
    exact MemLp.toLp_congr hf hg hfg
  · have hg : ¬ MemLp (g q) 2 μ := fun hg => hf ((memLp_congr_ae hfg).mpr hg)
    simp only [toL2Section, dite_eq_right hf, dite_eq_right hg]

/-- Jointly measurable representatives give a strongly measurable total
L² section map, even if square integrability holds only almost everywhere
in the parameter. -/
theorem stronglyMeasurable_toL2Section {f : Q → X → H}
    (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable (toL2Section (μ := μ) f) := by
  classical
  let good : Set Q := {q | MemLp (f q) 2 μ}
  have hgood : MeasurableSet good := by
    have heq : good = {q | Integrable (fun x => ‖f q x‖ ^ 2) μ} := by
      ext q
      exact memLp_two_iff_integrable_sq_norm hf.of_uncurry_left.aestronglyMeasurable
    rw [heq]
    exact measurableSet_integrable (hf.norm.pow 2)
  let g : Q → X → H := fun q x => if q ∈ good then f q x else 0
  have hg : StronglyMeasurable (Function.uncurry g) := by
    convert hf.indicator (hgood.preimage measurable_fst) using 1
    funext p
    simp only [g, Function.uncurry_def, Set.indicator_apply, mem_preimage]
  have hgm (q : Q) : MemLp (g q) 2 μ := by
    by_cases hq : MemLp (f q) 2 μ
    · simpa only [g, good, mem_ofPred_eq, ite_eq_left hq] using hq
    · apply (memLp_two_iff_integrable_sq_norm
        hg.of_uncurry_left.aestronglyMeasurable).mpr
      simp [g, good, hq]
  have hs := stronglyMeasurable_toL2_sections hg hgm
  convert hs using 1
  funext q
  by_cases hq : MemLp (f q) 2 μ
  · simp only [toL2Section, dite_eq_left hq, g, good, mem_ofPred_eq, ite_eq_left hq]
  · simp only [toL2Section, dite_eq_right hq, g, good, mem_ofPred_eq, ite_eq_right hq]
    exact (MemLp.toLp_zero _).symm

omit [SFinite μ] [IsSeparable μ] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H] in
/-- On the full-measure set of finite-mass parameters, the total section
map represents the original function. -/
theorem toL2Section_ae_represents {ν : Measure Q} {f : Q → X → H}
    (hLp : ∀ᵐ q ∂ν, MemLp (f q) 2 μ) :
    ∀ᵐ q ∂ν, (toL2Section (μ := μ) f q : X → H) =ᵐ[μ] f q := by
  filter_upwards [hLp] with q hq
  rw [toL2Section_eq hq]
  exact hq.coeFn_toLp

variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]

omit [TopologicalSpace.SeparableSpace H] in
/-- The pointwise coordinate repair is jointly strongly measurable whenever
the lifted multiplier and source representatives are jointly so. -/
theorem channelValue_jointly_stronglyMeasurable
    (b : HilbertBasis ℕ ℂ V) {z : Q → X → V} {ψ : Q → X → H}
    (hz : StronglyMeasurable (Function.uncurry z))
    (hψ : StronglyMeasurable (Function.uncurry ψ)) (a : ℕ) :
    StronglyMeasurable (Function.uncurry (fun q => channelValue b (z q) (ψ q) a)) := by
  exact ((innerSL ℂ (b a)).continuous.comp_stronglyMeasurable hz).smul hψ

/-- Parameter measurability of the actual channel vectors follows from
jointly measurable inputs and the source mass estimate. -/
theorem channelVector_stronglyMeasurable
    (b : HilbertBasis ℕ ℂ V) {z : Q → X → V} {ψ : Q → X → H}
    (hz : StronglyMeasurable (Function.uncurry z))
    (hψ : StronglyMeasurable (Function.uncurry ψ))
    (hunit : ∀ q, ∀ᵐ x ∂μ, ‖z q x‖ = 1)
    (hmass : ∀ q, Integrable (fun x => ‖ψ q x‖ ^ 2) μ) (a : ℕ) :
    StronglyMeasurable (fun q => channelVector b
      hz.of_uncurry_left.aestronglyMeasurable hψ.of_uncurry_left.aestronglyMeasurable
      (hunit q) (hmass q) a) :=
  stronglyMeasurable_toL2_sections (channelValue_jointly_stronglyMeasurable b hz hψ a)
    (fun q => channelValue_memLp b hz.of_uncurry_left.aestronglyMeasurable
      hψ.of_uncurry_left.aestronglyMeasurable (hunit q) (hmass q) a)

/-- The same argument applies to the derived channel gradients. Their L²
membership follows from the proved energy identity rather than an
independent integrability assumption for each coordinate. -/
theorem channelDerivativeVector_stronglyMeasurable
    (b : HilbertBasis ℕ ℂ V) {z dz : Q → X → V} {u ψ : Q → X → H}
    {s : Q → X → ℝ}
    (hz : StronglyMeasurable (Function.uncurry z))
    (hdz : StronglyMeasurable (Function.uncurry dz))
    (hu : StronglyMeasurable (Function.uncurry u))
    (hψ : StronglyMeasurable (Function.uncurry ψ))
    (hunit : ∀ q, ∀ᵐ x ∂μ, ‖z q x‖ = 1)
    (hconn : ∀ q, ∀ᵐ x ∂μ, inner ℂ (z q x) (dz q x) = Complex.I * s q x)
    (henergy : ∀ q, Integrable (fun x => ‖u q x‖ ^ 2 +
      2 * s q x * (inner ℂ (u q x) (ψ q x)).re +
      ‖dz q x‖ ^ 2 * ‖ψ q x‖ ^ 2) μ) (a : ℕ) :
    StronglyMeasurable (fun q => channelDerivativeVector b
      hz.of_uncurry_left.aestronglyMeasurable hdz.of_uncurry_left.aestronglyMeasurable
      hu.of_uncurry_left.aestronglyMeasurable hψ.of_uncurry_left.aestronglyMeasurable
      (hunit q) (hconn q) (henergy q) a) := by
  apply stronglyMeasurable_toL2_sections
  exact (((innerSL ℂ (b a)).continuous.comp_stronglyMeasurable hz).smul hu).sub
    ((((innerSL ℂ (b a)).continuous.comp_stronglyMeasurable hdz).smul hψ).const_smul Complex.I)

variable [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- The physical coordinate channel can now be integrated over its
parameter. Joint representative measurability and integrable source mass
supply every vector and operator measurability obligation. -/
theorem channelOperator_integrable
    {ν : Measure Q} (R : Gaussian.RankOneData (Lp H 2 μ) T)
    (b : HilbertBasis ℕ ℂ V) {z : Q → X → V} {ψ : Q → X → H}
    (hz : StronglyMeasurable (Function.uncurry z))
    (hψ : StronglyMeasurable (Function.uncurry ψ))
    (hunit : ∀ q, ∀ᵐ x ∂μ, ‖z q x‖ = 1)
    (hmass : ∀ q, Integrable (fun x => ‖ψ q x‖ ^ 2) μ)
    (hmassint : Integrable (fun q => ∫ x, ‖ψ q x‖ ^ 2 ∂μ) ν) :
    Integrable (fun q => rankOneSeries R (fun a => channelVector b
      hz.of_uncurry_left.aestronglyMeasurable hψ.of_uncurry_left.aestronglyMeasurable
      (hunit q) (hmass q) a)) ν := by
  apply rankOneSeries_integrable R
    (fun a => (channelVector_stronglyMeasurable b hz hψ hunit hmass a).aestronglyMeasurable)
    _ hmassint
  exact Filter.Eventually.of_forall fun q => channelVector_mass b
    hz.of_uncurry_left.aestronglyMeasurable hψ.of_uncurry_left.aestronglyMeasurable
    (hunit q) (hmass q)

/-- Gaussian conditioning need only give finite mass and normalization at
almost every parameter. The default-zero L² sections remove the need to
supply separate all-parameter representatives. -/
theorem channelOperator_integrable_of_ae_mass
    {ν : Measure Q} (R : Gaussian.RankOneData (Lp H 2 μ) T)
    (b : HilbertBasis ℕ ℂ V) {z : Q → X → V} {ψ : Q → X → H}
    (hz : StronglyMeasurable (Function.uncurry z))
    (hψ : StronglyMeasurable (Function.uncurry ψ))
    (hunit : ∀ᵐ q ∂ν, ∀ᵐ x ∂μ, ‖z q x‖ = 1)
    (hmass : ∀ᵐ q ∂ν, Integrable (fun x => ‖ψ q x‖ ^ 2) μ)
    (hmassint : Integrable (fun q => ∫ x, ‖ψ q x‖ ^ 2 ∂μ) ν) :
    Integrable (fun q => rankOneSeries R (fun a =>
      toL2Section (μ := μ) (fun r => channelValue b (z r) (ψ r) a) q)) ν := by
  apply rankOneSeries_integrable R
    (fun a => (stronglyMeasurable_toL2Section
      (channelValue_jointly_stronglyMeasurable b hz hψ a)).aestronglyMeasurable)
    _ hmassint
  filter_upwards [hunit, hmass] with q hq hm
  convert channelVector_mass b hz.of_uncurry_left.aestronglyMeasurable
    hψ.of_uncurry_left.aestronglyMeasurable hq hm using 1
  funext a
  rw [toL2Section_eq (f := fun r => channelValue b (z r) (ψ r) a) (q := q)
    (channelValue_memLp b hz.of_uncurry_left.aestronglyMeasurable
      hψ.of_uncurry_left.aestronglyMeasurable hq hm a)]
  rfl

end GptLean.Repair
