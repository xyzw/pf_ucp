import GptLean.RepresentabilityDisplacementEstimate
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
The density-weighted measure used by the displacement equation is the
actual measure rho(x) dx. Weighted L2 conditions and energies are related
to their ordinary Lebesgue integral formulations, including densities
which vanish on sets of positive volume.
-/

noncomputable section
set_option Elab.async false

namespace GptLean.Representability

open MeasureTheory
open scoped ENNReal InnerProductSpace

def densityMeasure (ρ : DisplacementPosition → ℝ) : Measure DisplacementPosition :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

theorem densityMeasure_absolutelyContinuous (ρ : DisplacementPosition → ℝ) :
    densityMeasure ρ ≪ volume := withDensity_absolutelyContinuous _ _

theorem densityMeasure_finite {ρ : DisplacementPosition → ℝ}
    (hρ : Integrable ρ volume) : IsFiniteMeasure (densityMeasure ρ) :=
  isFiniteMeasure_withDensity_ofReal hρ.2

theorem densityMeasure_mass {ρ : DisplacementPosition → ℝ}
    (hρ : Integrable ρ volume) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) :
    (measureUnivNNReal (densityMeasure ρ) : ℝ) = ∫ x, ρ x := by
  change ((densityMeasure ρ) Set.univ).toReal = _
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (integral_eq_lintegral_of_nonneg_ae hρ0 hρ.1).symm

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem densityMeasure_integral {ρ : DisplacementPosition → ℝ}
    (hρ : AEStronglyMeasurable ρ volume) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    (f : DisplacementPosition → H) :
    (∫ x, f x ∂densityMeasure ρ) = ∫ x, ρ x • f x := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀
    hρ.aemeasurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ0] with x hx
  rw [ENNReal.toReal_ofReal hx]

theorem densityMeasure_integrable_iff {ρ : DisplacementPosition → ℝ}
    (hρ : AEStronglyMeasurable ρ volume) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    (f : DisplacementPosition → H) :
    Integrable f (densityMeasure ρ) ↔ Integrable (fun x => ρ x • f x) volume := by
  rw [densityMeasure, integrable_withDensity_iff_integrable_smul₀'
    hρ.aemeasurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [hρ0] with x hx
  rw [ENNReal.toReal_ofReal hx]

omit [NormedSpace ℝ H] in
theorem densityMeasure_memLp_two_iff {ρ : DisplacementPosition → ℝ}
    (hρ : AEStronglyMeasurable ρ volume) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    (f : DisplacementPosition → H) (hf : AEStronglyMeasurable f volume) :
    MemLp f 2 (densityMeasure ρ) ↔
      Integrable (fun x => ρ x * ‖f x‖ ^ 2) volume := by
  rw [memLp_two_iff_integrable_sq_norm
    (hf.mono_ac (densityMeasure_absolutelyContinuous ρ))]
  exact densityMeasure_integrable_iff hρ hρ0 _

/-- An equality for the weighted measure becomes an equality of physical
density-weighted fields, with no lower bound on the density. -/
theorem densityMeasure_smul_eq_ae {ρ : DisplacementPosition → ℝ}
    (hρ : AEStronglyMeasurable ρ volume) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    {f g : DisplacementPosition → H} (he : f =ᵐ[densityMeasure ρ] g) :
    (fun x => ρ x • f x) =ᵐ[volume] fun x => ρ x • g x := by
  have hh := (ae_withDensity_iff' hρ.aemeasurable.ennreal_ofReal).mp he
  filter_upwards [hρ0, hh] with x hx hh
  by_cases hz : ρ x = 0
  · simp only [hz, zero_smul]
  · have hp : 0 < ρ x := lt_of_le_of_ne hx (Ne.symm hz)
    rw [hh (ne_of_gt (ENNReal.ofReal_pos.mpr hp))]

variable [InnerProductSpace ℝ H]

omit [NormedSpace ℝ H] in
theorem l2_norm_sq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → H} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← Lp.norm_toLp f hf, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

omit [NormedSpace ℝ H] in
theorem densityMeasure_l2_norm_sq {ρ : DisplacementPosition → ℝ}
    (hρ : AEStronglyMeasurable ρ volume) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    (f : DisplacementPosition → H) (hf : MemLp f 2 (densityMeasure ρ)) :
    (eLpNorm f 2 (densityMeasure ρ)).toReal ^ 2 =
      ∫ x, ρ x * ‖f x‖ ^ 2 := by
  rw [l2_norm_sq_integral hf, densityMeasure_integral hρ hρ0]
  rfl

end GptLean.Representability
