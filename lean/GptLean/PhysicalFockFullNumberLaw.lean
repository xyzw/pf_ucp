import GptLean.PhysicalFockChannelNumberL2
import GptLean.PhysicalFockVacuumSectors
import GptLean.PhysicalFockFullGentle
import GptLean.PhotonLocalizationFockNumber

/-!
The retained/discarded probability law of the actual coupled channel.
Every mass is the trace of a concrete joint-sector projection. The
discarded mass equals the true vacuum defect and supplies the gentle
bound. The final cutoff instance discharges vacuum positivity separately
using its constructed square root.
-/

noncomputable section
namespace GptLean.PhysicalFock.FullNumberLaw

open MeasureTheory PhotonLocalizationChannel PhotonLocalizationFockChannel
open PhysicalNormalTrace ChannelNumber
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  (BF : StandardSymmetricFockExponential) (BT : StandardNormalTraceBackground)
  (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))

private theorem weight_bound (w : NumberWeight) (n : ℕ) : |w.val n| ≤ 1 := by
  rw [abs_of_nonneg (w.property n).1]
  exact (w.property n).2

def tail (M : ℕ) : BT.Trace (Lp PhotonFock 2 μ) →L[ℝ] ℝ :=
  fullNumberTest μ BT (tailWeight M).val (weight_bound (tailWeight M))

def weight : BT.Trace (Lp PhotonFock 2 μ) →L[ℝ] ℝ :=
  fullNumberTest μ BT geometricWeight.val (weight_bound geometricWeight)

theorem joint_nonneg (p : ℕ × ℕ) {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    0 ≤ fullJointEffect μ BF BT j p x :=
  BT.normal.observable_nonneg _ (fun u => by rw [fullJointEffect_rankOne]; positivity) hx

private theorem lifted_discard_hasSum (u : Lp PhotonFock 2 μ) :
    HasSum (fun p : ℕ × ℕ => (if 1 ≤ p.2 then (1 : ℝ) else 0) *
      ‖(jointCoordinate photonMeasure (photonExponential BF) j p).compLpL 2 μ u‖ ^ 2)
      (‖u‖ ^ 2 - ‖(VacuumOperator.operator photonMeasure
        (photonExponential BF) j).compLpL 2 μ u‖ ^ 2) := by
  have hpure (v : PhotonFock) :
      HasSum (fun p : ℕ × ℕ => (if 1 ≤ p.2 then (1 : ℝ) else 0) *
        ‖jointCoordinate photonMeasure (photonExponential BF) j p v‖ ^ 2)
        (‖v‖ ^ 2 - ‖VacuumOperator.operator photonMeasure (photonExponential BF) j v‖ ^ 2) := by
    simpa only [ite_mul, one_mul, zero_mul, jointCoordinate_apply,
      TensorSectors.pairCoordinate_apply, VacuumOperator.operator,
      ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.norm_map] using
      VacuumSectors.nonvac_mass_hasSum BF ((photonExponential BF).split photonMeasure j v)
  have h := @PhysicalL2QuadraticSeries.lift_norm_defect_hasSum X PhotonFock
    (inferInstance : MeasurableSpace X) μ
    (inferInstance : NormedAddCommGroup PhotonFock)
    (inferInstance : InnerProductSpace ℂ PhotonFock) (ℕ × ℕ) inferInstance
    (fun p : ℕ × ℕ => TensorCoordinates.TensorSpace
      (Sector photonMeasure p.1) (Sector photonMeasure p.2))
    (fun p => inferInstance) (fun p => inferInstance)
    (jointCoordinate photonMeasure (photonExponential BF) j)
    (fun p => if 1 ≤ p.2 then 1 else 0)
    (VacuumOperator.operator photonMeasure (photonExponential BF) j)
    (fun p => by split_ifs <;> norm_num) hpure u
  exact h

theorem discard_eq {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    PhotonLoss.discardProb (fun p => fullJointEffect μ BF BT j p x) =
      FullGentle.lossEffect μ BF BT j x := by
  have h : HasSum (fun p : ℕ × ℕ =>
      (if 1 ≤ p.2 then (1 : ℝ) else 0) * fullJointEffect μ BF BT j p x)
      (FullGentle.lossEffect μ BF BT j x) := by
    apply BT.normal.measurement_weighted (fullJointEffect μ BF BT j)
      (FullGentle.lossEffect μ BF BT j) (fun p => if 1 ≤ p.2 then 1 else 0)
      (fun p => by split_ifs <;> norm_num)
      (fun p u => by rw [fullJointEffect_rankOne]; positivity) _ hx
    intro u
    simpa only [fullJointEffect_rankOne, FullGentle.lossEffect_rankOne,
      FullGentle.vacuumOperator] using lifted_discard_hasSum μ BF j u
  simpa only [PhotonLoss.discardProb, ite_mul, one_mul, zero_mul] using h.tsum_eq

def numberLaw
    (hp : ∀ v, ‖VacuumOperator.operator photonMeasure (photonExponential BF) j v‖ ^ 2 ≤
      (⟪v, VacuumOperator.operator photonMeasure (photonExponential BF) j v⟫_ℂ).re)
    {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive)
    (htr : (BT.realization (Lp PhotonFock 2 μ)).rank.trace x = 1) :
    PhotonLoss.LocalizationNumberLaw (fun M x => tail μ BT M x) (fun x => weight μ BT x)
      x (BT.normal.extend ((electronicFactorization μ (photonFactorization BF)).factor j) x) where
  p p := fullJointEffect μ BF BT j p x
  nonneg p := joint_nonneg μ BF BT j p hx
  summable := (fullJointEffect_hasSum μ BF BT j hx).summable
  normalized := (fullJointEffect_hasSum μ BF BT j hx).tsum_eq.trans htr
  tail_eq M := by
    simpa only [tail, tailWeight, PhotonLoss.tailIn, ite_mul, one_mul, zero_mul] using
      (full_retained_hasSum μ BF BT j (tailWeight M).val (weight_bound (tailWeight M))
        (fun n => ((tailWeight M).property n).1) hx).tsum_eq.symm
  weight_in := by
    simpa only [weight, geometricWeight, PhotonLoss.bIn] using
      (full_retained_hasSum μ BF BT j geometricWeight.val (weight_bound geometricWeight)
        (fun n => (geometricWeight.property n).1) hx).tsum_eq.symm
  weight_total := by
    simpa only [weight, geometricWeight, PhotonLoss.bTot] using
      (full_total_hasSum μ BF BT j geometricWeight.val (weight_bound geometricWeight)
        (fun n => (geometricWeight.property n).1) hx).tsum_eq.symm
  gentle :=
    (FullGentle.gentle_of_photon_positive μ BF BT j hp hx htr).trans_eq
      (congrArg PhotonLoss.lossModulus (discard_eq μ BF BT j hx).symm)

end GptLean.PhysicalFock.FullNumberLaw
