import GptLean.PhysicalSectorCoordinates
import GptLean.PhysicalFockRadiation

/-!
Exact mass and radiation integrals after separating the finite photon
polarization fiber. All integrals are extended nonnegative integrals, so
the radiation identity also holds for vectors of infinite energy.
-/

noncomputable section
namespace GptLean.PhysicalSectorCoordinates

open MeasureTheory PhysicalFock PhysicalSectorMeasures
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

theorem l2_enorm_sq_lintegral {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X} (u : Lp H 2 μ) :
    ‖u‖ₑ ^ 2 = ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ := by
  have hn := Repair.toL2_norm_sq (Lp.memLp u)
  simp only [Lp.toLp_coeFn] at hn
  calc
    ‖u‖ₑ ^ 2 = ENNReal.ofReal (‖u‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal (∫ x, ‖u x‖ ^ 2 ∂μ) := congrArg ENNReal.ofReal hn
    _ = ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal
        ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u))
        (ae_of_all _ fun x => sq_nonneg ‖u x‖)
    _ = _ := by simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Scalar momentum weights do not see the regrouping of polarizations. -/
theorem fullMomentum_weighted (m : ℕ) (u : FullSector photonMeasure m)
    (w : Configuration m → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ k, w (modeEquiv m k).1 * ‖u k‖ₑ ^ 2 ∂SectorMeasure photonMeasure m) =
      ∫⁻ ξ, w ξ * ‖fullMomentum m u ξ‖ₑ ^ 2 := by
  rw [← (mode_measurePreserving m).symm.lintegral_comp_emb
    (modeEquiv m).symm.measurableEmbedding]
  simp only [MeasurableEquiv.apply_symm_apply]
  rw [lintegral_prod _ (by
    exact (hw.comp measurable_fst).aemeasurable.mul
      (((Lp.stronglyMeasurable u).comp_measurable (modeEquiv m).symm.measurable).enorm.pow_const 2).aemeasurable)]
  apply lintegral_congr_ae
  filter_upwards [fullMomentum_represents_ae m u] with ξ hξ
  calc
    (∫⁻ p, w ξ * ‖u ((modeEquiv m).symm (ξ, p))‖ₑ ^ 2 ∂Measure.count) =
        ∫⁻ p, w ξ * ‖fullMomentum m u ξ p‖ₑ ^ 2 ∂Measure.count := by
      apply lintegral_congr
      intro p
      rw [hξ p]
    _ = w ξ * ∫⁻ p, ‖fullMomentum m u ξ p‖ₑ ^ 2 ∂Measure.count :=
      lintegral_const_mul _ ((Lp.stronglyMeasurable (fullMomentum m u ξ)).enorm.pow_const 2)
    _ = _ := congrArg (w ξ * ·) (l2_enorm_sq_lintegral (fullMomentum m u ξ)).symm

def momentumRadiationSymbol (m : ℕ) (ξ : Configuration m) : ℝ :=
  ∑ j : Fin m, ‖SymmetricLift.particle ξ j‖

theorem momentumRadiationSymbol_measurable (m : ℕ) :
    Measurable (momentumRadiationSymbol m) := by
  unfold momentumRadiationSymbol
  have hp (j : Fin m) : Measurable (fun ξ : Configuration m => ‖SymmetricLift.particle ξ j‖) :=
    (SymmetricLift.particleLinear j).toContinuousLinearMap.continuous.norm.measurable
  fun_prop

/-- The actual sector radiation form in the same momentum coordinates as Rellich. -/
theorem sectorRadiationForm_momentum (m : ℕ) (u : Sector photonMeasure m) :
    sectorRadiationForm m u =
      ∫⁻ ξ, ENNReal.ofReal (momentumRadiationSymbol m ξ) * ‖sectorMomentum m u ξ‖ₑ ^ 2 := by
  have h := fullMomentum_weighted m u.val
    (fun ξ => ENNReal.ofReal (momentumRadiationSymbol m ξ))
    (momentumRadiationSymbol_measurable m).ennreal_ofReal
  have hs (k : Fin m → PhotonMode) :
      momentumRadiationSymbol m (modeEquiv m k).1 = sectorDispersion m k := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
  change sectorRadiationForm m u =
    ∫⁻ ξ, ENNReal.ofReal (momentumRadiationSymbol m ξ) * ‖fullMomentum m u.val ξ‖ₑ ^ 2
  simpa only [sectorRadiationForm, hs, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    using h

end GptLean.PhysicalSectorCoordinates
