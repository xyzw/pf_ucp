import GptLean.RemovalRepair
import GptLean.Repair.LiftSections
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
A common measurable representative of the actual lifted repair field and
its weak gradient. The fixed operator and its fixed derivative each have
one exceptional configuration set, independent of the Gaussian parameter.
All channel properties transfer through the same countable isometry.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.SymmetricLift

open MeasureTheory Filter TopologicalSpace

variable {Q : Type*} [MeasurableSpace Q]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [SeparableSpace V] [CompleteSpace V]

theorem TensorMultilinearData.configurationInsertion_jointly_stronglyMeasurable
    {B : TensorBackground V} (T : TensorMultilinearData B) {N : ℕ} (i : Fin N)
    {t g : Q → EuclideanSpace ℝ (Fin 3) → V}
    (ht : StronglyMeasurable (Function.uncurry t))
    (hg : StronglyMeasurable (Function.uncurry g)) :
    StronglyMeasurable (Function.uncurry (fun q =>
      configurationTensorInsertion B i (t q) (g q))) := by
  classical
  borelize V
  apply (T.pure_continuous N).comp_stronglyMeasurable
  apply Measurable.stronglyMeasurable
  apply measurable_pi_lambda
  intro j
  by_cases hji : j = i
  · subst j
    simpa [Function.update_self, Function.comp_def, Function.uncurry, particleLinear] using hg.measurable.comp
      (measurable_fst.prodMk
        ((particleLinear i).toContinuousLinearMap.continuous.measurable.comp measurable_snd))
  · simpa [Function.update_of_ne hji, Function.comp_def, Function.uncurry, particleLinear] using ht.measurable.comp
      (measurable_fst.prodMk
        ((particleLinear j).toContinuousLinearMap.continuous.measurable.comp measurable_snd))

def liftGradientRepresentative (B : TensorBackground V) (N : ℕ)
    (t : Q → EuclideanSpace ℝ (Fin 3) → V)
    (g : Q → Fin 3 → EuclideanSpace ℝ (Fin 3) → V)
    (j : Fin N × Fin 3) (q : Q) (x : Configuration N) :
    (recursiveLiftCandidate B N).target :=
  ((recursiveLiftOperator_fderiv_aestronglyMeasurable B N).mk
    (fderiv ℝ (recursiveLiftCandidate B N).operator) x (EuclideanSpace.single j 1))
      (configurationTensor B (t q) x) +
  (recursiveLiftOperator_aestronglyMeasurable B N).mk
    (recursiveLiftCandidate B N).operator x
      (configurationTensorInsertion B j.1 (t q) (g q j.2) x)

theorem liftGradientRepresentative_jointly_stronglyMeasurable
    (B : TensorBackground V) (T : TensorMultilinearData B) (N : ℕ)
    {t : Q → EuclideanSpace ℝ (Fin 3) → V}
    {g : Q → Fin 3 → EuclideanSpace ℝ (Fin 3) → V}
    (ht : StronglyMeasurable (Function.uncurry t))
    (hg : ∀ j, StronglyMeasurable (Function.uncurry (fun q => g q j)))
    (j : Fin N × Fin 3) :
    StronglyMeasurable (Function.uncurry (liftGradientRepresentative B N t g j)) := by
  have happ := (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := B.H N)
    (F := (recursiveLiftCandidate B N).target)).continuous
  exact (happ.comp_stronglyMeasurable
    ((StronglyMeasurable.apply_continuousLinearMap (𝕜 := ℝ)
      ((recursiveLiftOperator_fderiv_aestronglyMeasurable B N).stronglyMeasurable_mk.comp_measurable
      (measurable_snd : Measurable (Prod.snd : Q × Configuration N → Configuration N)))
        (EuclideanSpace.single j 1)).prodMk
      (T.configurationTensor_jointly_stronglyMeasurable N ht))).add
    (happ.comp_stronglyMeasurable
      (((recursiveLiftOperator_aestronglyMeasurable B N).stronglyMeasurable_mk.comp_measurable
        measurable_snd).prodMk
        (T.configurationInsertion_jointly_stronglyMeasurable j.1 ht (hg j.2))))

omit [MeasurableSpace Q] in
theorem liftGradientRepresentative_ae_eq (B : TensorBackground V) (N : ℕ)
    (t : Q → EuclideanSpace ℝ (Fin 3) → V)
    (g : Q → Fin 3 → EuclideanSpace ℝ (Fin 3) → V) :
    ∀ᵐ x ∂volume, ∀ j q, liftGradientRepresentative B N t g j q x =
      recursiveLiftWeakGradient B N (t q) (g q) j x := by
  filter_upwards [(recursiveLiftOperator_aestronglyMeasurable B N).ae_eq_mk,
    (recursiveLiftOperator_fderiv_aestronglyMeasurable B N).ae_eq_mk] with x hL hdL
  intro j q
  simp only [liftGradientRepresentative, recursiveLiftWeakGradient,
    recursiveLiftWeakDerivative, recursiveLiftCorrection, recursiveLiftField,
    Pi.add_apply, ← hL, ← hdL]

end GptLean.SymmetricLift

namespace GptLean.Repair

open MeasureTheory Filter TopologicalSpace GptLean.SymmetricLift

variable {Q ι : Type*} [MeasurableSpace Q]

def measuredRepairLift (B : TensorBackground SixTag) (N : ℕ)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    (t : Q → RepairSpace → SixTag) (q : Q) (x : Configuration N) : CountableTarget :=
  countableEmbedding basis index (liftSectionRepresentative B N t q x)

def measuredRepairGradient (B : TensorBackground SixTag) (N : ℕ)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    (t : Q → RepairSpace → SixTag) (g : Q → Fin 3 → RepairSpace → SixTag)
    (j : Fin N × Fin 3) (q : Q) (x : Configuration N) : CountableTarget :=
  countableEmbedding basis index (liftGradientRepresentative B N t g j q x)

theorem measuredRepairLift_stronglyMeasurable
    (B : TensorBackground SixTag) (T : TensorMultilinearData B) (N : ℕ)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    {t : Q → RepairSpace → SixTag} (ht : StronglyMeasurable (Function.uncurry t)) :
    StronglyMeasurable (Function.uncurry (measuredRepairLift B N basis index t)) :=
  (countableEmbedding basis index).continuous.comp_stronglyMeasurable
    (liftSectionRepresentative_jointly_stronglyMeasurable B T N ht)

theorem measuredRepairGradient_stronglyMeasurable
    (B : TensorBackground SixTag) (T : TensorMultilinearData B) (N : ℕ)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    {t : Q → RepairSpace → SixTag} {g : Q → Fin 3 → RepairSpace → SixTag}
    (ht : StronglyMeasurable (Function.uncurry t))
    (hg : ∀ j, StronglyMeasurable (Function.uncurry (fun q => g q j)))
    (j : Fin N × Fin 3) :
    StronglyMeasurable (Function.uncurry (measuredRepairGradient B N basis index t g j)) :=
  (countableEmbedding basis index).continuous.comp_stronglyMeasurable
    (liftGradientRepresentative_jointly_stronglyMeasurable B T N ht hg j)

omit [MeasurableSpace Q] in
theorem measuredRepairLift_weak
    (B : TensorBackground SixTag) (T : TensorMultilinearData B) (N : ℕ)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    {t : Q → RepairSpace → SixTag} {g : Q → Fin 3 → RepairSpace → SixTag}
    (q : Q) (ht : HasWeakH1Local (t q) (g q)) (hu : ∀ y, ‖t q y‖ = 1) :
    HasWeakH1Local (measuredRepairLift B N basis index t q)
      (fun j => measuredRepairGradient B N basis index t g j q) := by
  let := recursiveLiftCandidate_complete B N
  apply countableEmbedding_hasWeakH1Local basis index
  apply (recursiveLift_hasWeakH1Local B T N ht (fun y => (hu y).le)).congr
  · exact (liftSectionRepresentative_ae_eq B N t).mono (fun _ h => (h q).symm)
  · intro j
    exact (liftGradientRepresentative_ae_eq B N t g).mono (fun _ h => (h j q).symm)

omit [MeasurableSpace Q] in
theorem measuredRepairLift_unit
    (B : TensorBackground SixTag) (N : ℕ)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    {t : Q → RepairSpace → SixTag} (q : Q) (hu : ∀ y, ‖t q y‖ = 1) :
    ∀ᵐ x ∂volume, ‖measuredRepairLift B N basis index t q x‖ = 1 := by
  filter_upwards [liftSectionRepresentative_ae_eq B N t,
    recursiveLift_unit_ae B N (Eventually.of_forall hu)] with x hx hxunit
  simpa only [measuredRepairLift, countableEmbedding_norm, hx q] using hxunit

omit [MeasurableSpace Q] in
theorem measuredRepairLift_connection
    (B : TensorBackground SixTag) (T : TensorMultilinearData B) (N : ℕ)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    {t : Q → RepairSpace → SixTag} {g : Q → Fin 3 → RepairSpace → SixTag}
    {s : Q → Fin 3 → RepairSpace → ℝ} (q : Q)
    (hu : ∀ y, ‖t q y‖ = 1)
    (hc : ∀ j y, inner ℂ (t q y) (g q j y) = Complex.I * s q j y)
    (j : Fin N × Fin 3) :
    ∀ᵐ x ∂volume, inner ℂ (measuredRepairLift B N basis index t q x)
      (measuredRepairGradient B N basis index t g j q x) =
        Complex.I * s q j.2 (particle x j.1) := by
  filter_upwards [liftSectionRepresentative_ae_eq B N t,
    liftGradientRepresentative_ae_eq B N t g,
    recursiveLift_connection_ae B T N j (g q) (Eventually.of_forall hu)] with x hx hdx hconn
  simpa only [measuredRepairLift, measuredRepairGradient, countableEmbedding_inner,
    hx q, hdx j q, hc] using hconn

omit [MeasurableSpace Q] in
theorem measuredRepairLift_metric
    (B : TensorBackground SixTag) (T : TensorMultilinearData B) (N : ℕ)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    (V M : Q → ℝ) (v : Q → (Fin 3 → ℝ) → Fin 3 → ℝ) (q : Q)
    (hV : 0 ≤ V q) (hM : 0 ≤ M q) (hv : Differentiable ℝ (v q))
    (hvV : ∀ x j, |v q x j| ≤ V q)
    (hdv : ∀ x, ∑ i, ∑ j,
      (fderiv ℝ (v q) x (Pi.single j (1 : ℝ)) i) ^ 2 ≤ M q ^ 2) :
    ∀ᵐ x ∂volume, (∑ j, ‖measuredRepairGradient B N basis index
      (fun q => repairTag (V q) (M q) (v q))
      (fun q => repairTagGradient (V q) (M q) (v q)) j q x‖ ^ 2) ≤
        9 * ((N : ℝ) + liftMetricConstant N) * (36 * V q ^ 2 + 2 * M q) := by
  filter_upwards [liftGradientRepresentative_ae_eq B N
    (fun q => repairTag (V q) (M q) (v q))
    (fun q => repairTagGradient (V q) (M q) (v q)),
    repairLift_metric B T N hV hM hv hvV hdv] with x hx hm
  simpa only [measuredRepairGradient, countableEmbedding_norm, hx] using hm

end GptLean.Repair
