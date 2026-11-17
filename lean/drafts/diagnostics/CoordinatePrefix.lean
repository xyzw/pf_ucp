import PfHk.CoordinateMultiplication
import PfHk.CoordinateComparisonSpectral
import PfHk.PhysicalMultiplierField
import PfHk.ScalarCoefficientNormAlgebra

/-!
The physical endpoint multipliers are consequences of the ordinary
Hilbert-valued coordinate Sobolev embedding and commuting spectral calculus.
All products are actual L2 functions, represented by `roughMultiply_ae`.
The quantized-field contribution uses the proved pointwise creation and
annihilation estimate and requires no spatial derivative of the field.
-/

noncomputable section
namespace PfHk.PhysicalCoordinateMultipliers

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalOperatorDomain PfHk.PhysicalDyadicIntegralFractional
open PfHk.PhysicalLocalEnergy PfHk.CoordinateSobolev
open GptLean.PhysicalSourceCoordinates
open scoped ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 5000

attribute [local irreducible] PhysicalPFReference.inclusion
  PhysicalPFReference.ordinary PhysicalPFReference.radiation
  PhysicalPFReference.field PhysicalPFReference.covariant

local instance endpointPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

variable {N : ℕ}

theorem sum_hasMultiplier {J : Type*} (s : Finset J)
    (b : J → Configuration N → ℝ) (u : WaveSpace (Fin N × Fin 3))
    (hb : ∀ j ∈ s, HasMultiplier (b j) u) :
    HasMultiplier (fun x => ∑ j ∈ s, b j x) u := by
  unfold HasMultiplier at hb ⊢
  simpa only [Finset.sum_smul] using memLp_finsetSum s hb

theorem square_memLp_three {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {b : X → ℝ} (hb : MemLp b 6 μ) : MemLp (fun x => b x ^ 2) 3 μ := by
  let : ENNReal.HolderTriple 6 6 3 :=
    ENNReal.HolderTriple.of_toReal ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [pow_two] using (show MemLp (fun x => b x * b x) 3 μ from hb.mul' hb)

theorem square_lpNorm {X : Type*} [MeasurableSpace X] (μ : Measure X) (b : X → ℝ) :
    (eLpNorm (fun x => b x ^ 2) 3 μ).toReal = (eLpNorm b 6 μ).toReal ^ 2 := by
  have he := eLpNorm_norm_rpow (μ := μ) (p := (3 : ℝ≥0∞)) b
    (by norm_num : (0 : ℝ) < 2)
  norm_num [Real.rpow_two, Real.norm_eq_abs, sq_abs, ENNReal.rpow_two] at he
  rw [he, ENNReal.toReal_pow]

theorem bounded_multiplier (b : Configuration N → ℝ) (hb : MemLp b ∞ volume)
    (u : WaveSpace (Fin N × Fin 3)) :
    ∃ hm : HasMultiplier b u,
      ‖roughMultiply b u hm‖ ^ 2 ≤ (eLpNorm b ∞ volume).toReal ^ 2 * ‖u‖ ^ 2 := by
  exact ScalarCoefficientNormAlgebra.bounded_multiplier (H := PhotonFock) b hb u

def coefficientNormSq (S : CoordinateSobolev.Data PhotonFock N)
    (q : ℝ) (b : Position → ℝ) : ℝ :=
  (S.constant q) ^ 2 * (eLpNorm b (ENNReal.ofReal q) volume).toReal ^ 2

theorem coefficientNormSq_nonneg (S : CoordinateSobolev.Data PhotonFock N)
    (q : ℝ) (b : Position → ℝ) : 0 ≤ coefficientNormSq S q b := by
  unfold coefficientNormSq
  positivity

theorem coefficientNormSq_square (S : CoordinateSobolev.Data PhotonFock N)
    (b : Position → ℝ) : coefficientNormSq S 3 (fun x => b x ^ 2) =
      (S.constant 3) ^ 2 * (eLpNorm b 6 volume).toReal ^ 4 := by
  norm_num only [coefficientNormSq, ENNReal.ofReal_ofNat]
  rw [square_lpNorm]
  ring


end PfHk.PhysicalCoordinateMultipliers
