import GptLean.PhysicalFockSpatialField
import GptLean.PhotonLocalizationLocalForms

/-! Bounded scalar multiplication on complex Banach-valued L2, including
the radiation graph with its actual graph norm. -/

noncomputable section

namespace GptLean.PhysicalBoundedScalar

open MeasureTheory PhysicalFock PhotonLocalization
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

variable {X H K : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  (μ : Measure X) (f : X → ℝ) (hf : AEStronglyMeasurable f μ)
  (M : ℝ) (hb : ∀ᵐ x ∂μ, |f x| ≤ M)

include hb in
private theorem scalarOperator_bound :
    ∀ᵐ x ∂μ, ‖(f x : ℂ) • ContinuousLinearMap.id ℂ H‖ ≤ M := by
  filter_upwards [hb] with x hx
  rw [norm_smul]
  calc
    ‖(f x : ℂ)‖ * ‖ContinuousLinearMap.id ℂ H‖ ≤ ‖(f x : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ ≤ M := by simpa only [mul_one, Complex.norm_real, Real.norm_eq_abs] using hx

def multiplier : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  spatialOperator μ (fun x => (f x : ℂ) • ContinuousLinearMap.id ℂ H)
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hf).smul aestronglyMeasurable_const)
    M (scalarOperator_bound (H := H) μ f M hb)

theorem multiplier_ae (u : Lp H 2 μ) :
    multiplier μ f hf M hb u =ᵐ[μ] fun x => (f x : ℂ) • u x :=
  spatialOperator_ae μ _ _ _ _ u

theorem multiplier_norm_le (u : Lp H 2 μ) :
    ‖multiplier μ f hf M hb u‖ ≤ M * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplier_ae μ f hf M hb u, hb] with x hx hfx
  rw [hx, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hfx (norm_nonneg _)

theorem multiplier_compLpL (L : H →L[ℂ] K) (u : Lp H 2 μ) :
    L.compLpL 2 μ (multiplier μ f hf M hb u) =
      multiplier μ f hf M hb (L.compLpL 2 μ u) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (multiplier μ f hf M hb u),
    multiplier_ae μ f hf M hb u,
    multiplier_ae μ f hf M hb (L.compLpL 2 μ u), L.coeFn_compLpL u]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, map_smul]

theorem multiplier_spatialOperator
    (A : X → H →L[ℂ] K) (hA : AEStronglyMeasurable A μ)
    (D : ℝ) (hD : ∀ᵐ x ∂μ, ‖A x‖ ≤ D) (u : Lp H 2 μ) :
    spatialOperator μ A hA D hD (multiplier μ f hf M hb u) =
      multiplier μ f hf M hb (spatialOperator μ A hA D hD u) := by
  apply Lp.ext
  filter_upwards [spatialOperator_ae μ A hA D hD (multiplier μ f hf M hb u),
    multiplier_ae μ f hf M hb u,
    multiplier_ae μ f hf M hb (spatialOperator μ A hA D hD u),
    spatialOperator_ae μ A hA D hD u] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, map_smul]

section Hilbert
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem multiplier_eq_realL2 :
    multiplier (H := F) μ f hf M hb = realL2Multiplier f hf M hb := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [multiplier_ae μ f hf M hb u,
    realL2Multiplier_apply f hf M hb u] with x hx hy
  rw [hx, hy, Complex.coe_smul]

end Hilbert
end GptLean.PhysicalBoundedScalar
