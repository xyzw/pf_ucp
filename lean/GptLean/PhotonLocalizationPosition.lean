import GptLean.PhotonLocalizationLocalFormsCutoff
import GptLean.PhotonLocalizationLocalFormsOperators
import GptLean.PhotonLocalizationNormalTrace

/-! The electronic position calculus is actual multiplication on the
spatial L² space. The trace formula for arbitrary bounded tests therefore
identifies the same electronic cutoff as the weak-form construction. -/

noncomputable section

namespace GptLean.PhotonLocalization

open MeasureTheory
open scoped BoundedContinuousFunction

variable {N : ℕ} {K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def positionMultiplier (f : (Fin N → ElectronicPosition) →ᵇ ℝ) :
    SpatialPhotonL2 (Fin N × Fin 3) K →L[ℂ] SpatialPhotonL2 (Fin N × Fin 3) K :=
  realL2Multiplier (fun x => f (electronicPositions x))
    (f.continuous.comp electronicPositions.continuous).aestronglyMeasurable ‖f‖
    (ae_of_all _ fun x => f.norm_coe_le_norm (electronicPositions x))

theorem positionMultiplier_apply (f : (Fin N → ElectronicPosition) →ᵇ ℝ)
    (u : SpatialPhotonL2 (Fin N × Fin 3) K) :
    positionMultiplier f u =ᵐ[volume] fun x => f (electronicPositions x) • u x :=
  realL2Multiplier_apply _ _ _ _ _

def positionObservable : ((Fin N → ElectronicPosition) →ᵇ ℝ) →+*
    (SpatialPhotonL2 (Fin N × Fin 3) K →L[ℂ] SpatialPhotonL2 (Fin N × Fin 3) K) where
  toFun := positionMultiplier
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [positionMultiplier_apply (0 : (Fin N → ElectronicPosition) →ᵇ ℝ) u,
      Lp.coeFn_zero K 2 volume] with x hx hz
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, zero_smul,
      zero_apply, hz] using hx
  map_one' := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [positionMultiplier_apply (1 : (Fin N → ElectronicPosition) →ᵇ ℝ) u]
      with x hx
    simpa only [BoundedContinuousFunction.coe_one, Pi.one_apply, one_smul,
      one_apply_eq_self] using hx
  map_add' f g := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [positionMultiplier_apply (f + g) u,
      positionMultiplier_apply f u, positionMultiplier_apply g u,
      Lp.coeFn_add (positionMultiplier f u) (positionMultiplier g u)] with x h₁ h₂ h₃ h₄
    change positionMultiplier (f + g) u x = (positionMultiplier f u + positionMultiplier g u) x
    simp only [h₁, h₄, Pi.add_apply, h₂, h₃, BoundedContinuousFunction.add_apply, add_smul]
  map_mul' f g := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [positionMultiplier_apply (f * g) u,
      positionMultiplier_apply f (positionMultiplier g u), positionMultiplier_apply g u]
      with x h₁ h₂ h₃
    change positionMultiplier (f * g) u x = positionMultiplier f (positionMultiplier g u) x
    simp only [h₁, h₂, h₃, BoundedContinuousFunction.mul_apply, mul_smul]

theorem positionObservable_selfadjoint [CompleteSpace K]
    (f : (Fin N → ElectronicPosition) →ᵇ ℝ) :
    IsSelfAdjoint (positionObservable (K := K) f) :=
  realL2Multiplier_selfadjoint (fun x => f (electronicPositions x))
    (f.continuous.comp electronicPositions.continuous).aestronglyMeasurable ‖f‖
    (ae_of_all _ fun x => f.norm_coe_le_norm (electronicPositions x))

theorem positionObservable_cutoff (L : ℝ) (hL : 0 < L) :
    positionObservable (K := K) (electronicProductBCF L) =
      (physicalElectronicCutoff (N := N) L hL).operator := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [positionMultiplier_apply (electronicProductBCF L) u,
    (physicalElectronicCutoff (N := N) L hL).operator_apply u] with x h₁ h₂
  exact h₁.trans h₂.symm

/-- The standard position trace formula now supplies the physical trace
data using the same multiplication operators as the weak-form proof. -/
def physicalPositionTrace [CompleteSpace K]
    (φ : (SpatialPhotonL2 (Fin N × Fin 3) K →L[ℂ]
      SpatialPhotonL2 (Fin N × Fin 3) K) →L[ℂ] ℂ)
    (ν : Measure (Fin N → ElectronicPosition))
    (htrace : ∀ f, (φ (positionObservable f)).re = ∫ x, f x ∂ν) :
    ElectronicPositionTrace φ ν where
  observable := positionObservable
  selfadjoint := positionObservable_selfadjoint
  trace := htrace

end GptLean.PhotonLocalization
