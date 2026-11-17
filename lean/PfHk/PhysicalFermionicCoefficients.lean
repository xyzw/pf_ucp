import PfHk.PhysicalCommonFormCoefficients
import PfHk.PhysicalCoulombUCPCoefficients

/-! The article's local regularity for one common external vector and scalar
potential, together with their existing global coefficient classes. These
hypotheses construct the physical UCP data for the identical-particle form. -/

noncomputable section
namespace PfHk.PhysicalFermionicCoefficients

open MeasureTheory GptLean GptLean.PhysicalPairDuality
  GptLean.PhysicalSourceCoordinates PfHk.FriedrichsDivergenceBackground
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

structure Regularity (A : VectorPotential) (v : ScalarPotential) where
  exponent : ℝ
  exponent_gt_two : 2 < exponent
  divergence : Position → ℝ
  vector_local : ∀ j (o : Position) (r : ℝ), 0 < r →
    MemLp (fun x => A.val x j) 6 (volume.restrict (Metric.ball o r))
  scalar_local : ∀ (o : Position) (r : ℝ), 0 < r →
    MemLp (v.val : Position → ℝ) (ENNReal.ofReal exponent)
      (volume.restrict (Metric.ball o r))
  divergence_local : ∀ (o : Position) (r : ℝ), 0 < r →
    MemLp divergence (ENNReal.ofReal exponent) (volume.restrict (Metric.ball o r))
  weak_divergence : WeakDivergence (fun j x => A.val x j) divergence

variable {N : ℕ} {A : VectorPotential} {v : ScalarPotential}

def Regularity.data (h : Regularity A v) (c : ℝ) (hc : 0 ≤ c) :
    PhysicalUCPCoefficients.Data N (GptLean.SymmetricLift.distinctConfigurations N) :=
  PhysicalCoulombUCPCoefficients.data (PhysicalCommonFormDomain.vectorCoefficient A)
    (fun _ => h.divergence) (fun _ => (v.val : Position → ℝ))
    h.exponent h.exponent h.exponent_gt_two h.exponent_gt_two
    (fun _ => h.vector_local) (fun _ => h.divergence_local) (fun _ => h.scalar_local)
    (fun _ => h.weak_divergence) (fun _ => ⟨v, Filter.EventuallyEq.rfl⟩) c hc

@[simp] theorem Regularity.data_vector (h : Regularity A v) (c : ℝ) (hc : 0 ≤ c) :
    (h.data (N := N) c hc).vector = PhysicalCommonFormDomain.vector A := rfl

@[simp] theorem Regularity.data_scalar (h : Regularity A v) (c : ℝ) (hc : 0 ≤ c) :
    (h.data (N := N) c hc).scalar = PhysicalCommonFormDomain.scalar v c := rfl

@[simp] theorem Regularity.data_positive (h : Regularity A v) (c : ℝ) (hc : 0 ≤ c) :
    (h.data (N := N) c hc).positive = PhysicalCommonFormDomain.positive v c := rfl

@[simp] theorem Regularity.data_negative (h : Regularity A v) (c : ℝ) (hc : 0 ≤ c) :
    (h.data (N := N) c hc).negative = PhysicalCommonFormDomain.negative v c := rfl

end PfHk.PhysicalFermionicCoefficients
