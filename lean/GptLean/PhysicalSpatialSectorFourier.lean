import GptLean.PhysicalFourierFubini
import GptLean.PhysicalSectorCoordinates

/-!
Exact joint Fourier coordinates for the physical spatial photon sectors.
The photon inverse Fourier map cancels the photon part of the joint
transform. The resulting weighted integral is the iterated electronic
Fourier and photon momentum integral, with no normalization factor.
-/

noncomputable section
namespace GptLean.PhysicalSectorCoordinates

open MeasureTheory PhysicalFock PhysicalSectorMeasures
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

def configurationIsometry (N m : ℕ) : Configuration (N + m) ≃ₗᵢ[ℝ]
    WithLp 2 (Configuration N × Configuration m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (configurationIndex N m).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2
      (fun _ : (Fin N × Fin 3) ⊕ (Fin m × Fin 3) => ℝ))

@[simp] theorem configurationIsometry_ofLp (N m : ℕ) (x : Configuration (N + m)) :
    WithLp.ofLp (configurationIsometry N m x) = configurationSplit N m x := rfl

section Join
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

def spatialJoin (N m : ℕ) :
    Lp (Lp H 2 (volume : Measure (Configuration m))) 2
        (volume : Measure (Configuration N)) →ₗᵢ[ℂ]
      Lp H 2 (volume : Measure (Configuration (N + m))) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (configurationSplit N m)
    (configurationSplit_measurePreserving N m)).comp
      PhysicalSourceFubini.curryEquiv.symm.toLinearIsometry

private theorem spatialJoin_eq (N m : ℕ)
    (u : Lp (Lp H 2 (volume : Measure (Configuration m))) 2
      (volume : Measure (Configuration N))) :
    spatialJoin N m u =
      Lp.compMeasurePreservingₗᵢ ℂ (configurationIsometry N m)
        (configurationIsometry N m).measurePreserving (PhysicalFourierFubini.join u) :=
  Lp.compMeasurePreserving_comp_apply (PhysicalSourceFubini.curryEquiv.symm u)
    (WithLp.volume_preserving_ofLp (Configuration N) (Configuration m))
    (configurationIsometry N m).measurePreserving

theorem fourier_spatialJoin (N m : ℕ)
    (u : Lp (Lp H 2 (volume : Measure (Configuration m))) 2
      (volume : Measure (Configuration N))) :
    Lp.fourierTransformₗᵢ (Configuration (N + m)) H (spatialJoin N m u) =
      spatialJoin N m
        ((Lp.fourierTransformₗᵢ (Configuration m) H).toLinearIsometry.toContinuousLinearMap.compLpL
          2 volume (Lp.fourierTransformₗᵢ (Configuration N)
            (Lp H 2 (volume : Measure (Configuration m))) u)) := by
  let pull := Lp.compMeasurePreservingₗᵢ ℂ (configurationIsometry N m)
    (configurationIsometry N m).measurePreserving (E := H) (p := 2)
  exact (congrArg (Lp.fourierTransformₗᵢ (Configuration (N + m)) H)
    (spatialJoin_eq N m u)).trans
      ((PhysicalL2FourierTransport.fourier_pull (configurationIsometry N m)
        (PhysicalFourierFubini.join u)).trans
        ((congrArg pull (PhysicalFourierFubini.fourier_join u)).trans
          (spatialJoin_eq N m _).symm))

theorem spatialJoin_weighted (N m : ℕ)
    (u : Lp (Lp H 2 (volume : Measure (Configuration m))) 2
      (volume : Measure (Configuration N)))
    (w : Configuration N × Configuration m → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ ξ, w (configurationSplit N m ξ) * ‖spatialJoin N m u ξ‖ₑ ^ 2) =
      ∫⁻ x, ∫⁻ y, w (x, y) * ‖u x y‖ₑ ^ 2 := by
  let v : Lp H 2 ((volume : Measure (Configuration N)).prod
      (volume : Measure (Configuration m))) := PhysicalSourceFubini.curryEquiv.symm u
  have hv : PhysicalSourceFubini.curryEquiv v = u :=
    LinearIsometryEquiv.apply_symm_apply _ _
  have hrep := PhysicalSourceFubini.curryEquiv_represents_ae v
  rw [hv] at hrep
  calc
    _ = ∫⁻ ξ, w (configurationSplit N m ξ) *
        ‖v (configurationSplit N m ξ)‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_compMeasurePreserving v
        (configurationSplit_measurePreserving N m)] with ξ hξ
      exact congrArg (fun z : H => w (configurationSplit N m ξ) * ‖z‖ₑ ^ 2) hξ
    _ = ∫⁻ z, w z * ‖v z‖ₑ ^ 2 ∂((volume : Measure (Configuration N)).prod
        (volume : Measure (Configuration m))) :=
      (configurationSplit_measurePreserving N m).lintegral_comp_emb
        (configurationSplit N m).toHomeomorph.measurableEmbedding
          (fun z => w z * ‖v z‖ₑ ^ 2)
    _ = ∫⁻ x, ∫⁻ y, w (x, y) * ‖v (x, y)‖ₑ ^ 2 :=
      lintegral_prod _ (hw.aemeasurable.mul ((Lp.stronglyMeasurable v).enorm.pow_const 2).aemeasurable)
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hrep] with x hx
      apply lintegral_congr_ae
      filter_upwards [hx] with y hy
      exact congrArg (fun z : H => w (x, y) * ‖z‖ₑ ^ 2) hy.symm
end Join

private theorem fourier_position_lift (N m : ℕ)
    (u : Lp (Sector photonMeasure m) 2 (volume : Measure (Configuration N))) :
    (Lp.fourierTransformₗᵢ (Configuration m) (Coefficient m)).toLinearIsometry.toContinuousLinearMap.compLpL
        2 volume (liftIsometry volume (sectorPosition m) u) =
      liftIsometry volume (sectorMomentum m) u := by
  apply Lp.ext
  filter_upwards [
    (Lp.fourierTransformₗᵢ (Configuration m) (Coefficient m)).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL
      (liftIsometry volume (sectorPosition m) u),
    liftIsometry_ae volume (sectorPosition m) u,
    liftIsometry_ae volume (sectorMomentum m) u] with x hF hp hm
  have hc : Lp.fourierTransformₗᵢ (Configuration m) (Coefficient m)
      (sectorPosition m (u x)) = sectorMomentum m (u x) :=
    LinearIsometryEquiv.apply_symm_apply _ _
  exact hF.trans ((congrArg (Lp.fourierTransformₗᵢ (Configuration m) (Coefficient m)) hp).trans
    (hc.trans hm.symm))

/-- The joint transform cancels the photon inverse transform and retains the electronic transform. -/
theorem spatialSectorPosition_fourier (N m : ℕ)
    (u : Lp (Sector photonMeasure m) 2 (volume : Measure (Configuration N))) :
    Lp.fourierTransformₗᵢ (Configuration (N + m)) (Coefficient m)
        (spatialSectorPosition N m u) =
      spatialJoin N m (liftIsometry volume (sectorMomentum m)
        (Lp.fourierTransformₗᵢ (Configuration N) (Sector photonMeasure m) u)) := by
  have hp : spatialSectorPosition N m u =
      spatialJoin N m (liftIsometry volume (sectorPosition m) u) := rfl
  have hf : Lp.fourierTransformₗᵢ (Configuration N)
      (Lp (Coefficient m) 2 (volume : Measure (Configuration m)))
      (liftIsometry volume (sectorPosition m) u) =
    liftIsometry volume (sectorPosition m)
      (Lp.fourierTransformₗᵢ (Configuration N) (Sector photonMeasure m) u) :=
    PhysicalL2FourierTransport.fourier_compLpL
      (sectorPosition m).toContinuousLinearMap u
  let L := (Lp.fourierTransformₗᵢ (Configuration m) (Coefficient m)).toLinearIsometry.toContinuousLinearMap.compLpL
    2 (volume : Measure (Configuration N))
  exact (congrArg (Lp.fourierTransformₗᵢ (Configuration (N + m)) (Coefficient m)) hp).trans
    ((fourier_spatialJoin N m (liftIsometry volume (sectorPosition m) u)).trans
      (congrArg (spatialJoin N m)
        ((congrArg L hf).trans (fourier_position_lift N m _))))

/-- Exact weighted joint Fourier energy in electronic Fourier and photon momentum coordinates. -/
theorem spatialSectorPosition_fourier_weighted (N m : ℕ)
    (u : Lp (Sector photonMeasure m) 2 (volume : Measure (Configuration N)))
    (w : Configuration N × Configuration m → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ ξ, w (configurationSplit N m ξ) *
        ‖Lp.fourierTransformₗᵢ (Configuration (N + m)) (Coefficient m)
          (spatialSectorPosition N m u) ξ‖ₑ ^ 2) =
      ∫⁻ x, ∫⁻ y, w (x, y) *
        ‖sectorMomentum m
          (Lp.fourierTransformₗᵢ (Configuration N) (Sector photonMeasure m) u x) y‖ₑ ^ 2 := by
  apply Eq.trans (congrArg
    (fun v : Lp (Coefficient m) 2 (volume : Measure (Configuration (N + m))) =>
      ∫⁻ ξ, w (configurationSplit N m ξ) * ‖v ξ‖ₑ ^ 2)
    (spatialSectorPosition_fourier N m u))
  apply Eq.trans (spatialJoin_weighted N m _ w hw)
  apply lintegral_congr_ae
  filter_upwards [liftIsometry_ae volume (sectorMomentum m)
    (Lp.fourierTransformₗᵢ (Configuration N) (Sector photonMeasure m) u)] with x hx
  exact congrArg (fun v : Lp (Coefficient m) 2 (volume : Measure (Configuration m)) =>
    ∫⁻ y, w (x, y) * ‖v y‖ₑ ^ 2) hx

end GptLean.PhysicalSectorCoordinates
