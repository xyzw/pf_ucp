import GptLean.Repair.LiftChannel
import GptLean.Repair.ParameterSections
import GptLean.Repair.CountableFrame

/-!
Measurable parameter sections for the actual recursive tensor lift.
One strongly measurable operator representative is chosen independently
of the parameter. Its exceptional configuration set therefore works for
every source field at once. Equality in L² transfers the resulting joint
measurability back to the actual channel vectors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.SymmetricLift

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

variable {Q : Type*} [MeasurableSpace Q]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]

/-- Finite tensor products preserve joint measurability in the conditioning
parameter and the full electron configuration. -/
theorem TensorMultilinearData.configurationTensor_jointly_stronglyMeasurable
    {B : TensorBackground V} (M : TensorMultilinearData B) (N : ℕ)
    {t : Q → EuclideanSpace ℝ (Fin 3) → V}
    (ht : StronglyMeasurable (Function.uncurry t)) :
    StronglyMeasurable (Function.uncurry (fun q => configurationTensor B (t q) (N := N))) := by
  borelize V
  apply (M.pure_continuous N).comp_stronglyMeasurable
  apply Measurable.stronglyMeasurable
  apply measurable_pi_lambda
  intro i
  exact ht.measurable.comp (measurable_fst.prodMk
    ((particleLinear i).toContinuousLinearMap.continuous.measurable.comp measurable_snd))

/-- A representative of the lifted field using one fixed measurable
representative of the recursive operator. -/
def liftSectionRepresentative (B : TensorBackground V) (N : ℕ)
    (t : Q → EuclideanSpace ℝ (Fin 3) → V) (q : Q) (x : Configuration N) :
    (recursiveLiftCandidate B N).target :=
  (recursiveLiftOperator_aestronglyMeasurable B N).mk
    (recursiveLiftCandidate B N).operator x (configurationTensor B (t q) x)

theorem liftSectionRepresentative_jointly_stronglyMeasurable
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    {t : Q → EuclideanSpace ℝ (Fin 3) → V}
    (ht : StronglyMeasurable (Function.uncurry t)) :
    StronglyMeasurable (Function.uncurry (liftSectionRepresentative B N t)) := by
  exact (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := B.H N)
    (F := (recursiveLiftCandidate B N).target)).continuous.comp_stronglyMeasurable
    (((recursiveLiftOperator_aestronglyMeasurable B N).stronglyMeasurable_mk.comp_measurable
      measurable_snd).prodMk
        (M.configurationTensor_jointly_stronglyMeasurable N ht))

omit [MeasurableSpace Q] in
/-- The exceptional set is independent of the parameter, including when
the parameter space is uncountable. -/
theorem liftSectionRepresentative_ae_eq (B : TensorBackground V) (N : ℕ)
    (t : Q → EuclideanSpace ℝ (Fin 3) → V) :
    ∀ᵐ x ∂volume, ∀ q,
      liftSectionRepresentative B N t q x =
        recursiveLiftField B N (configurationTensor B (t q)) x := by
  filter_upwards [(recursiveLiftOperator_aestronglyMeasurable B N).ae_eq_mk] with x hx
  intro q
  exact congrArg (fun L : B.H N →L[ℂ] (recursiveLiftCandidate B N).target =>
    L (configurationTensor B (t q) x)) hx.symm

omit [MeasurableSpace Q] in
/-- Normalization passes to the common measurable representative. -/
theorem liftSectionRepresentative_unit_ae (B : TensorBackground V) (N : ℕ)
    {t : Q → EuclideanSpace ℝ (Fin 3) → V}
    (ht : ∀ q, ∀ᵐ y ∂volume, ‖t q y‖ = 1) (q : Q) :
    ∀ᵐ x ∂volume, ‖liftSectionRepresentative B N t q x‖ = 1 := by
  filter_upwards [liftSectionRepresentative_ae_eq B N t,
    recursiveLift_unit_ae B N (ht q)] with x hx hu
  rw [hx q]
  exact hu

end GptLean.SymmetricLift

namespace GptLean.Repair

open MeasureTheory Filter TopologicalSpace GptLean.SymmetricLift
open scoped ENNReal Topology

variable {Q H : Type*} [MeasurableSpace Q]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [SeparableSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SeparableSpace H]

/-- The actual recursive lift supplies measurable L² Kraus sections from
joint one-particle and wavefunction representatives. No measurability of
the lifted field or of its L² channel vectors is assumed. -/
theorem recursiveLift_channelVector_stronglyMeasurable
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    (b : HilbertBasis ℕ ℂ (recursiveLiftCandidate B N).target)
    {t : Q → EuclideanSpace ℝ (Fin 3) → V} {ψ : Q → Configuration N → H}
    (ht : StronglyMeasurable (Function.uncurry t))
    (hψ : StronglyMeasurable (Function.uncurry ψ))
    (hunit : ∀ q, ∀ᵐ y ∂volume, ‖t q y‖ = 1)
    (hmass : ∀ q, Integrable (fun x => ‖ψ q x‖ ^ 2) volume) (a : ℕ) :
    StronglyMeasurable (fun q => channelVector b
      (recursiveLiftField_aestronglyMeasurable B N
        (M.aestronglyMeasurable_configurationTensor ht.of_uncurry_left.aestronglyMeasurable))
      hψ.of_uncurry_left.aestronglyMeasurable
      (recursiveLift_unit_ae B N (hunit q)) (hmass q) a) := by
  have hz := liftSectionRepresentative_jointly_stronglyMeasurable B M N ht
  have hzu := liftSectionRepresentative_unit_ae B N hunit
  have hrep := channelVector_stronglyMeasurable b hz hψ hzu hmass a
  convert hrep using 1
  funext q
  apply MemLp.toLp_congr
  filter_upwards [liftSectionRepresentative_ae_eq B N t] with x hx
  exact congrArg (fun z => coordinate b z a • ψ q x) (hx q).symm

/-- Default-zero sections give a total measurable L² channel without any
all-parameter mass or normalization assumptions. -/
theorem recursiveLift_channelSection_stronglyMeasurable
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    (b : HilbertBasis ℕ ℂ (recursiveLiftCandidate B N).target)
    {t : Q → EuclideanSpace ℝ (Fin 3) → V} {ψ : Q → Configuration N → H}
    (ht : StronglyMeasurable (Function.uncurry t))
    (hψ : StronglyMeasurable (Function.uncurry ψ)) (a : ℕ) :
    StronglyMeasurable (fun q => toL2Section (μ := volume)
      (fun r => channelValue b (recursiveLiftField B N (configurationTensor B (t r)))
        (ψ r) a) q) := by
  have hz := liftSectionRepresentative_jointly_stronglyMeasurable B M N ht
  have hrep := stronglyMeasurable_toL2Section (μ := volume)
    (channelValue_jointly_stronglyMeasurable b hz hψ a)
  convert hrep using 1
  funext q
  apply toL2Section_congr
  filter_upwards [liftSectionRepresentative_ae_eq B N t] with x hx
  exact congrArg (fun z => coordinate b z a • ψ q x) (hx q).symm

/-- The operator built from the actual recursive lift is Bochner
integrable under the almost-everywhere mass hypotheses supplied by
conditioning. No lifted-channel measurability premise remains. -/
theorem recursiveLift_channelOperator_integrable_of_ae_mass
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
    {ν : Measure Q}
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    (R : Gaussian.RankOneData (Lp H 2 (volume : Measure (Configuration N))) T)
    (b : HilbertBasis ℕ ℂ (recursiveLiftCandidate B N).target)
    {t : Q → EuclideanSpace ℝ (Fin 3) → V} {ψ : Q → Configuration N → H}
    (ht : StronglyMeasurable (Function.uncurry t))
    (hψ : StronglyMeasurable (Function.uncurry ψ))
    (hunit : ∀ᵐ q ∂ν, ∀ᵐ y ∂volume, ‖t q y‖ = 1)
    (hmass : ∀ᵐ q ∂ν, Integrable (fun x => ‖ψ q x‖ ^ 2) volume)
    (hmassint : Integrable (fun q => ∫ x, ‖ψ q x‖ ^ 2 ∂volume) ν) :
    Integrable (fun q => rankOneSeries R (fun a => toL2Section (μ := volume)
      (fun r => channelValue b (recursiveLiftField B N (configurationTensor B (t r)))
        (ψ r) a) q)) ν := by
  apply rankOneSeries_integrable R
    (fun a => (recursiveLift_channelSection_stronglyMeasurable B M N b ht hψ a).aestronglyMeasurable)
    _ hmassint
  filter_upwards [hunit, hmass] with q hq hm
  have hz := recursiveLiftField_aestronglyMeasurable B N
    (M.aestronglyMeasurable_configurationTensor (N := N) (t := t q)
      ht.of_uncurry_left.aestronglyMeasurable)
  have hu := recursiveLift_unit_ae B N hq
  convert channelVector_mass b hz hψ.of_uncurry_left.aestronglyMeasurable hu hm using 1
  funext a
  rw [toL2Section_eq (f := fun r => channelValue b
    (recursiveLiftField B N (configurationTensor B (t r))) (ψ r) a) (q := q)
    (channelValue_memLp b hz hψ.of_uncurry_left.aestronglyMeasurable hu hm a)]
  rfl

/-- A finite or countable lift target is first embedded into the standard
countable target. The fixed embedding preserves joint measurability. -/
theorem recursiveLift_countableChannelSection_stronglyMeasurable
    {ι : Type*} (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    (b : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (e : ι ↪ ℕ)
    {t : Q → EuclideanSpace ℝ (Fin 3) → V} {ψ : Q → Configuration N → H}
    (ht : StronglyMeasurable (Function.uncurry t))
    (hψ : StronglyMeasurable (Function.uncurry ψ)) (a : ℕ) :
    StronglyMeasurable (fun q => toL2Section (μ := volume)
      (fun r => channelValue countableTargetBasis
        (fun x => countableEmbedding b e
          (recursiveLiftField B N (configurationTensor B (t r)) x)) (ψ r) a) q) := by
  have hz := liftSectionRepresentative_jointly_stronglyMeasurable B M N ht
  have hze : StronglyMeasurable (Function.uncurry (fun q x =>
      countableEmbedding b e (liftSectionRepresentative B N t q x))) :=
    (countableEmbedding b e).continuous.comp_stronglyMeasurable hz
  have hrep := stronglyMeasurable_toL2Section (μ := volume)
    (channelValue_jointly_stronglyMeasurable countableTargetBasis hze hψ a)
  convert hrep using 1
  funext q
  apply toL2Section_congr
  filter_upwards [liftSectionRepresentative_ae_eq B N t] with x hx
  exact congrArg (fun z => coordinate countableTargetBasis (countableEmbedding b e z) a • ψ q x)
    (hx q).symm

/-- The actual recursive-lift channel is integrable for finite target
spaces as well as infinite ones. Conditioning hypotheses hold only almost
everywhere in the parameter. -/
theorem recursiveLift_countableChannelOperator_integrable_of_ae_mass
    {ι T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
    {ν : Measure Q}
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    (R : Gaussian.RankOneData (Lp H 2 (volume : Measure (Configuration N))) T)
    (b : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (e : ι ↪ ℕ)
    {t : Q → EuclideanSpace ℝ (Fin 3) → V} {ψ : Q → Configuration N → H}
    (ht : StronglyMeasurable (Function.uncurry t))
    (hψ : StronglyMeasurable (Function.uncurry ψ))
    (hunit : ∀ᵐ q ∂ν, ∀ᵐ y ∂volume, ‖t q y‖ = 1)
    (hmass : ∀ᵐ q ∂ν, Integrable (fun x => ‖ψ q x‖ ^ 2) volume)
    (hmassint : Integrable (fun q => ∫ x, ‖ψ q x‖ ^ 2 ∂volume) ν) :
    Integrable (fun q => rankOneSeries R (fun a => toL2Section (μ := volume)
      (fun r => channelValue countableTargetBasis
        (fun x => countableEmbedding b e
          (recursiveLiftField B N (configurationTensor B (t r)) x)) (ψ r) a) q)) ν := by
  apply rankOneSeries_integrable R
    (fun a => (recursiveLift_countableChannelSection_stronglyMeasurable B M N b e ht hψ a).aestronglyMeasurable)
    _ hmassint
  filter_upwards [hunit, hmass] with q hq hm
  have hz := countableEmbedding_aestronglyMeasurable b e
    (recursiveLiftField_aestronglyMeasurable B N
      (M.aestronglyMeasurable_configurationTensor (N := N) (t := t q)
        ht.of_uncurry_left.aestronglyMeasurable))
  have hu : ∀ᵐ x ∂volume, ‖countableEmbedding b e
      (recursiveLiftField B N (configurationTensor B (t q)) x)‖ = 1 := by
    simpa only [countableEmbedding_norm] using recursiveLift_unit_ae B N hq
  convert channelVector_mass countableTargetBasis hz
    hψ.of_uncurry_left.aestronglyMeasurable hu hm using 1
  funext a
  rw [toL2Section_eq (f := fun r => channelValue countableTargetBasis
    (fun x => countableEmbedding b e
      (recursiveLiftField B N (configurationTensor B (t r)) x)) (ψ r) a) (q := q)
    (channelValue_memLp countableTargetBasis hz
      hψ.of_uncurry_left.aestronglyMeasurable hu hm a)]
  rfl

end GptLean.Repair
