import GptLean.Gaussian.SpatialFieldWeak
import GptLean.SymmetricLift.BoundedMollification
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
Measurable smooth reconstruction from pathwise weak derivatives. Only the
ordinary deterministic all-orders Sobolev embedding is supplied as standard
background. The random smooth representative is defined by the same explicit
mollifier limit for every parameter, so its joint measurability is proved
rather than supplied by a measurable selection assumption.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Gaussian

open MeasureTheory Filter GptLean.SymmetricLift
open scoped ENNReal Topology ContDiff

/-- Ordinary deterministic local Sobolev regularity in dimension three.
This is a universal background statement about real functions. It makes no
reference to Gaussian fields, WIS, cutoffs, state weights or moments. -/
def SmoothSobolevBackground : Prop :=
  ∀ f : List (Fin 3) → FieldSpace → ℝ,
    (∀ ds, HasWeakH1Local (f ds) (fun j => f (j :: ds))) →
    ∃ g : List (Fin 3) → FieldSpace → ℝ,
      (∀ ds, ContDiff ℝ ∞ (g ds)) ∧
      (∀ ds, f ds =ᵐ[volume] g ds) ∧
      ∀ ds j x, HasLineDerivAt ℝ (g ds) (g (j :: ds) x) x (EuclideanSpace.single j 1)

/-- The reconstruction is an actual common mollifier limit. -/
def smoothSpatialRepresentative {Q : Type*} (field : List (Fin 3) → FieldSpace → Q → ℝ)
    (ds : List (Fin 3)) (x : FieldSpace) (q : Q) : ℝ :=
  limUnder atTop (fun n => boundedMollification (fun y => field ds y q) n x)

theorem jointly_measurable_smoothSpatialRepresentative
    {Q : Type*} [MeasurableSpace Q]
    (field : List (Fin 3) → FieldSpace → Q → ℝ)
    (hm : ∀ ds, Measurable (Function.uncurry (field ds))) (ds : List (Fin 3)) :
    Measurable (Function.uncurry (smoothSpatialRepresentative field ds)) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  have h : StronglyMeasurable (fun z : (FieldSpace × Q) × FieldSpace =>
      (approximationBump 3 n).normed volume (z.1.1 - z.2) * field ds z.2 z.1.2) := by
    apply Measurable.stronglyMeasurable
    exact (((approximationBump 3 n).continuous_normed.measurable.comp
      ((measurable_fst.comp measurable_fst).sub measurable_snd)).mul
        ((hm ds).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  exact h.integral_prod_right

theorem boundedMollification_eq_of_ae_eq {f g : FieldSpace → ℝ}
    (h : f =ᵐ[volume] g) (n : ℕ) (x : FieldSpace) :
    boundedMollification f n x = boundedMollification g n x := by
  apply integral_congr_ae
  filter_upwards [h] with y hy
  change (approximationBump 3 n).normed volume (x - y) • f y =
    (approximationBump 3 n).normed volume (x - y) • g y
  rw [hy]

theorem boundedMollification_tendsto_of_continuous {g : FieldSpace → ℝ}
    (hg : Continuous g) (x : FieldSpace) :
    Tendsto (fun n => boundedMollification g n x) atTop (𝓝 (g x)) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (approximationBump_rOut_tendsto 3) hg x
  simpa only [boundedMollification, smoothMollify, convolution_flip] using h

/-- All spatial derivatives share one Gaussian exceptional set. On its
complement the explicitly defined representative is smooth, agrees with the
original joint field almost everywhere in space, and has the specified
classical derivatives. The conclusion remains valid for any measure
absolutely continuous with respect to the original Gaussian measure. -/
theorem smooth_spatial_representative_of_weak
    {Q : Type*} [MeasurableSpace Q] {μ : Measure Q}
    (sobolev : SmoothSobolevBackground)
    (field : List (Fin 3) → FieldSpace → Q → ℝ)
    (hweak : ∀ᵐ q ∂μ, ∀ ds,
      HasWeakH1Local (fun x => field ds x q) (fun j x => field (j :: ds) x q)) :
    ∀ᵐ q ∂μ,
      (∀ ds, ContDiff ℝ ∞ (fun x => smoothSpatialRepresentative field ds x q)) ∧
      (∀ ds, (fun x => field ds x q) =ᵐ[volume]
        (fun x => smoothSpatialRepresentative field ds x q)) ∧
      (∀ ds j x, HasLineDerivAt ℝ (fun x => smoothSpatialRepresentative field ds x q)
        (smoothSpatialRepresentative field (j :: ds) x q) x (EuclideanSpace.single j 1)) := by
  filter_upwards [hweak] with q hq
  obtain ⟨g, hg, heq, hd⟩ := sobolev (fun ds x => field ds x q) hq
  have hs : ∀ ds x, smoothSpatialRepresentative field ds x q = g ds x := by
    intro ds x
    apply Tendsto.limUnder_eq
    have hlim := boundedMollification_tendsto_of_continuous (hg ds).continuous x
    exact hlim.congr (fun n =>
      (boundedMollification_eq_of_ae_eq (heq ds) n x).symm)
  refine ⟨?_, ?_, ?_⟩
  · intro ds
    simpa only [hs] using hg ds
  · intro ds
    simpa only [hs] using heq ds
  · intro ds j x
    simpa only [hs] using hd ds j x

end GptLean.Gaussian
