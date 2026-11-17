import GptLean.PhysicalFockVacuumFirst
import GptLean.PhysicalFockElectronicComposition
import GptLean.PhysicalFockVacuumPositive
import GptLean.PhysicalTraceMetric
import GptLean.PhysicalPhotonMarginalMoments

/-!
The gentle law on the actual coupled electronic/photon trace space.
Vacuum-first coordinates are constructed and shown to define the same
normal channel. Their first Kraus operator is the pointwise lift of the
actual Fock vacuum compression. Its positivity follows from the actual
square-root cutoff, not from a channel-level premise.
-/

noncomputable section
namespace GptLean.PhysicalFock.FullGentle

open MeasureTheory PhotonLocalizationChannel PhotonLocalizationFockChannel
open PhysicalNormalTrace
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

section Generic
variable {X H : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem compLp_positive_quadratic (A : H →L[ℂ] H)
    (h : ∀ v, ‖A v‖ ^ 2 ≤ (⟪v, A v⟫_ℂ).re) (u : Lp H 2 μ) :
    ‖A.compLpL 2 μ u‖ ^ 2 ≤ (⟪u, A.compLpL 2 μ u⟫_ℂ).re := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral, PhysicalPhotonMarginal.quadratic_integral]
  apply integral_mono_ae
  · exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  · exact PhysicalPhotonMarginal.quadratic_integrable A u
  · filter_upwards [A.coeFn_compLpL u] with x hx
    rw [hx]
    exact h (u x)

private theorem norm_sub_le_of_positive (u v : H)
    (h : ‖v‖ ^ 2 ≤ (⟪u, v⟫_ℂ).re) :
    ‖u - v‖ ^ 2 ≤ ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  change ‖u‖ ^ 2 - 2 * (⟪u, v⟫_ℂ).re + ‖v‖ ^ 2 ≤ ‖u‖ ^ 2 - ‖v‖ ^ 2
  linarith only [h]
end Generic

variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  (BF : StandardSymmetricFockExponential) (BT : StandardNormalTraceBackground)
  (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))

def vacuumOperator : Lp PhotonFock 2 μ →L[ℂ] Lp PhotonFock 2 μ :=
  (VacuumOperator.operator photonMeasure (photonExponential BF) j).compLpL 2 μ

theorem first_coordinate (u : Lp PhotonFock 2 μ) :
    KrausL2.lift μ (VacuumFirst.factor BF j) u 0 = vacuumOperator μ BF j u := by
  apply Lp.ext
  filter_upwards [KrausL2.lift_coordinate_ae μ (VacuumFirst.factor BF j) u 0,
    (VacuumOperator.operator photonMeasure (photonExponential BF) j).coeFn_compLpL u]
    with x h₁ h₂
  exact h₁.trans ((VacuumFirst.factor_zero BF j (u x)).trans h₂.symm)

theorem same_channel {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive) :
    BT.normal.extend (KrausL2.lift μ (VacuumFirst.factor BF j)) x =
      BT.normal.extend ((electronicFactorization μ (photonFactorization BF)).factor j) x :=
  PhysicalChannelDual.equal BT.normal (BT.realization (Lp PhotonFock 2 μ)).functional _ _
    (ElectronicComposition.lift_pullback_eq _ _ (VacuumFirst.pullback_eq BF j)) hx

def lossEffect : BT.Trace (Lp PhotonFock 2 μ) →L[ℝ] ℝ :=
  (BT.realization (Lp PhotonFock 2 μ)).rank.trace -
    (BT.realization (Lp PhotonFock 2 μ)).rank.trace.comp (BT.push (vacuumOperator μ BF j))

@[simp] theorem lossEffect_rankOne (u : Lp PhotonFock 2 μ) :
    lossEffect μ BF BT j ((BT.realization (Lp PhotonFock 2 μ)).rank.rankOne u) =
      ‖u‖ ^ 2 - ‖vacuumOperator μ BF j u‖ ^ 2 := by
  simp only [lossEffect, sub_apply, ContinuousLinearMap.comp_apply,
    BT.push_rankOne, Gaussian.RankOneData.trace_rankOne]

theorem gentle_of_photon_positive
    (hp : ∀ v, ‖VacuumOperator.operator photonMeasure (photonExponential BF) j v‖ ^ 2 ≤
      (⟪v, VacuumOperator.operator photonMeasure (photonExponential BF) j v⟫_ℂ).re)
    {x : BT.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (BT.realization (Lp PhotonFock 2 μ)).rank.positive)
    (htr : (BT.realization (Lp PhotonFock 2 μ)).rank.trace x = 1) :
    ‖x - BT.normal.extend ((electronicFactorization μ (photonFactorization BF)).factor j) x‖ ≤
      PhotonLoss.lossModulus (lossEffect μ BF BT j x) := by
  have hloss (u : Lp PhotonFock 2 μ) :
      lossEffect μ BF BT j ((BT.realization (Lp PhotonFock 2 μ)).rank.rankOne u) =
        ‖u‖ ^ 2 - ‖KrausL2.lift μ (VacuumFirst.factor BF j) u 0‖ ^ 2 :=
    (lossEffect_rankOne μ BF BT j u).trans
      (congrArg (fun v : Lp PhotonFock 2 μ => ‖u‖ ^ 2 - ‖v‖ ^ 2)
        (first_coordinate μ BF j u).symm)
  have hK (u : Lp PhotonFock 2 μ) :
      ‖u - KrausL2.lift μ (VacuumFirst.factor BF j) u 0‖ ^ 2 ≤
        ‖u‖ ^ 2 - ‖KrausL2.lift μ (VacuumFirst.factor BF j) u 0‖ ^ 2 := by
    have hu := compLp_positive_quadratic μ
      (VacuumOperator.operator photonMeasure (photonExponential BF) j) hp u
    have hn : ‖u - vacuumOperator μ BF j u‖ ^ 2 ≤
        ‖u‖ ^ 2 - ‖vacuumOperator μ BF j u‖ ^ 2 :=
      norm_sub_le_of_positive u (vacuumOperator μ BF j u) hu
    exact (congrArg (fun v : Lp PhotonFock 2 μ =>
      ‖u - v‖ ^ 2 ≤ ‖u‖ ^ 2 - ‖v‖ ^ 2) (first_coordinate μ BF j u)).mpr hn
  have h : ‖x - BT.normal.extend (KrausL2.lift μ (VacuumFirst.factor BF j)) x‖ ≤
      PhotonLoss.lossModulus (lossEffect μ BF BT j x) := BT.normal.gentle_state
    (rankOneMetric (BT.realization (Lp PhotonFock 2 μ)).functional)
    (KrausL2.lift μ (VacuumFirst.factor BF j)) (lossEffect μ BF BT j)
    hloss hK
    (show x ∈ BT.normal.states from ⟨hx, htr⟩)
  exact (congrArg (fun y : BT.Trace (Lp PhotonFock 2 μ) => ‖x - y‖)
    (same_channel μ BF BT j hx)).symm.trans_le h

end GptLean.PhysicalFock.FullGentle
