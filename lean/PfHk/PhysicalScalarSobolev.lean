import PfHk.PhysicalLocalEnergyCutoff
import PfHk.UniqueContinuationDensity
import PfHk.L2ScalarNorm

/-!
The density-point argument specialized to actual Pauli–Fierz eigenvectors.
The remaining functional-analysis input is the ordinary scalar Sobolev
inequality, quantified over arbitrary real weak H1 functions. Scalar cutoff
existence concerns only ordinary real functions and their first derivatives.
-/

noncomputable section
namespace PfHk.PhysicalInfiniteOrder

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy
open PfHk.UniqueContinuationDensity
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 10000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFScalarMultiplier.multiply
  PhysicalPFReference.ordinary PhysicalPFReference.radiation externalCovariant

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The scalar Sobolev inequality independently of the Pauli–Fierz model.
For dimension `d > 2` the exponent is `p = d/(d-2)`. -/
def ScalarSobolevBound (p S : ℝ) : Prop :=
  ∀ (f : Position I → ℝ) (g : I → Position I → ℝ),
    SymmetricLift.HasWeakH1Local f g → MemLp f 2 volume →
    (∀ i, MemLp (g i) 2 volume) →
      MemLp (fun x => f x ^ 2) (ENNReal.ofReal p) volume ∧
      (∫ x, (f x ^ 2) ^ p) ^ (1 / p) ≤ S * (∑ i, ∫ x, g i x ^ 2)

variable (V : Position I → ℝ)

theorem localized_norm_sq_ae (a : DifferentiableMultiplier I)
    (ha : ∀ x, 0 ≤ a.weight x) (u : Reference I V) :
    (fun x => ‖inclusion I V (PhysicalPFScalarMultiplier.multiply V a u) x‖ ^ 2) =ᵐ[volume]
      fun x => (a.weight x * ‖inclusion I V u x‖) ^ 2 := by
  have hv := PhysicalPFScalarMultiplier.value_multiply V a u
  have hnorm := PhysicalCutoffCommutator.scalar_multiplier_norm_sq_ae
    (H := PhotonFock) a ha (inclusion I V u)
  filter_upwards [hnorm] with x hx
  exact (congrArg (fun v : WaveSpace I => ‖v x‖ ^ 2) hv).trans hx

theorem localized_scalar_sobolev {p S : ℝ} (hSob : ScalarSobolevBound (I := I) p S)
    (a : DifferentiableMultiplier I) (ha : ∀ x, 0 ≤ a.weight x)
    (u : Reference I V) :
    MemLp (fun x => (a.weight x * ‖inclusion I V u x‖) ^ 2)
        (ENNReal.ofReal p) volume ∧
      (∫ x, ((a.weight x * ‖inclusion I V u x‖) ^ 2) ^ p) ^ (1 / p) ≤
        S * normGradientEnergy V (PhysicalPFScalarMultiplier.multiply V a u) := by
  let w := PhysicalPFScalarMultiplier.multiply V a u
  have hh := hSob (fun x => ‖inclusion I V w x‖) (normGradient V w)
    (normGradient_weak V w) (Lp.memLp _).norm (normGradient_memLp V w)
  have heq := localized_norm_sq_ae V a ha u
  refine ⟨(memLp_congr_ae heq).mp hh.1, ?_⟩
  have hint : (∫ x, ((a.weight x * ‖inclusion I V u x‖) ^ 2) ^ p) =
      ∫ x, (‖inclusion I V w x‖ ^ 2) ^ p := by
    apply integral_congr_ae
    filter_upwards [heq] with x hx using congrArg (fun z : ℝ => z ^ p) hx.symm
  rw [hint]
  exact hh.2


end PfHk.PhysicalInfiniteOrder
