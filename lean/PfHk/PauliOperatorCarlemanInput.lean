import PfHk.PauliPhysicalCarlemanModel
import PfHk.PhysicalUCPBackgrounds
import PfHk.PhysicalCarlemanCutoffPassage

/-! The bundled spinor mass estimate used in continuation. Its source is
 the actual orbital cutoff commutator acting on the coupled Pauli state. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PauliOperatorCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PauliLocalEnergy
  PfHk.PhysicalCommonFormDomain PfHk.CenteredPhysicalReference
  PfHk.PhysicalCutoffCommutator PfHk.SmoothCutoffBounds
  PfHk.PhysicalFieldRegularity PfHk.PhysicalLocalEnergy
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion rawForm

def sourceIntegrand (O : Configuration N) (α τ : ℝ)
    (f : PauliReference.Wave N) (X : Configuration N) : ℝ :=
  Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (dist X O))) *
    dist X O ^ 2 * ‖f X‖ ^ 2

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

def commutator (η : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N) : PauliReference.Wave N :=
  FiniteFiberL2.bundle (PauliLocalCutoffRules.commutator C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
    (vector A) (positive v c) (negative v c) η u (physicalDomain A v c hc u))

/-- The precise annular-cutoff estimate needed by the local propagation
proof. The weak equation is the coupled Pauli equation. -/
def CarlemanAt (E : ℝ) (O : Configuration N) (R α τ₀ K : ℝ) : Prop :=
  ∀ (u : Ref N),
    IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u) →
    ∀ (family : BufferedFamily O) (ε : ℝ), 0 < ε → ε ≤ R / 4 →
    ∀ τ : ℝ, τ₀ ≤ τ →
      (∫⁻ X in Metric.ball O R, ENNReal.ofReal
        (UniqueContinuation.radialMassIntegrand (fun X => dist X O)
          (PauliReference.wave (localize
            (twiceSub (family.cutoff (R / 2)) (family.cutoff ε)).scalar u)) α τ X)) ≤
        ENNReal.ofReal K * (∫⁻ X in Metric.ball O R, ENNReal.ofReal
          (sourceIntegrand O α τ
            (commutator F χ C e A v c hc
              (twiceSub (family.cutoff (R / 2)) (family.cutoff ε)) u) X))

def UniformLocalCarleman (E α : ℝ) (U : Set (Configuration N)) : Prop :=
  ∀ O ∈ U, ∃ R₀ τ₀ K : ℝ,
    0 < R₀ ∧ R₀ ≤ Real.exp (-2) ∧ 1 ≤ τ₀ ∧ 0 ≤ K ∧
    Metric.ball O (4 * R₀) ⊆ U ∧
    ∀ y ∈ Metric.ball O R₀, ∀ R : ℝ, 0 < R → R ≤ R₀ →
      CarlemanAt F χ C e A v c hc E y R α τ₀ K

end PfHk.PauliOperatorCarleman
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
