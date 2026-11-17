import GptLean.PhysicalGaussianCoordinates
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
Gaussian coordinates for the radiation and potential pair. The Hilbert
sum norm is retained exactly, so its L² norm is the sum of the two form
energies. The map is constructed from the same scalar realization in
each component.
-/

noncomputable section
namespace GptLean.PhysicalGaussianCoordinates

open MeasureTheory Filter
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {Q H K : Type*} [MeasurableSpace Q] (μ : Measure Q)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def pairL2Linear : WithLp 2 (Lp H 2 μ × Lp K 2 μ) →ₗ[ℂ]
    Lp (WithLp 2 (H × K)) 2 μ :=
  let E := (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap
  let L := E.comp (ContinuousLinearMap.inl ℂ H K)
  let R := E.comp (ContinuousLinearMap.inr ℂ H K)
  (L.compLpL 2 μ).toLinearMap.comp (WithLp.fstₗ 2 ℂ _ _) +
    (R.compLpL 2 μ).toLinearMap.comp (WithLp.sndₗ 2 ℂ _ _)

theorem pairL2Linear_ae (u : WithLp 2 (Lp H 2 μ × Lp K 2 μ)) :
    pairL2Linear μ u =ᵐ[μ] fun q => WithLp.toLp 2 (u.fst q, u.snd q) := by
  let E := (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap
  let L := E.comp (ContinuousLinearMap.inl ℂ H K)
  let R := E.comp (ContinuousLinearMap.inr ℂ H K)
  change (L.compLpL 2 μ u.fst + R.compLpL 2 μ u.snd) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_add (L.compLpL 2 μ u.fst) (R.compLpL 2 μ u.snd),
    L.coeFn_compLpL u.fst, R.coeFn_compLpL u.snd] with q hq hL hR
  rw [hq, Pi.add_apply, hL, hR]
  apply WithLp.ofLp_injective 2
  exact Prod.ext (add_zero _) (zero_add _)

theorem pairL2Linear_norm (u : WithLp 2 (Lp H 2 μ × Lp K 2 μ)) :
    ‖pairL2Linear μ u‖ = ‖u‖ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ K := InnerProductSpace.complexToReal
  have hi (v : Lp H 2 μ) : Integrable (fun q => ‖v q‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hj (v : Lp K 2 μ) : Integrable (fun q => ‖v q‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2,
    PhotonKernelLocalization.l2_norm_sq_eq_integral,
    PhotonKernelLocalization.l2_norm_sq_eq_integral,
    PhotonKernelLocalization.l2_norm_sq_eq_integral, ← integral_add (hi _) (hj _)]
  apply integral_congr_ae
  filter_upwards [pairL2Linear_ae μ u] with q hq
  rw [hq, WithLp.prod_norm_sq_eq_of_L2]
  rfl

def pairL2Isometry : WithLp 2 (Lp H 2 μ × Lp K 2 μ) →ₗᵢ[ℂ]
    Lp (WithLp 2 (H × K)) 2 μ where
  toLinearMap := pairL2Linear μ
  norm_map' := pairL2Linear_norm μ

theorem pairL2Isometry_surjective : Function.Surjective (pairL2Isometry μ (H := H) (K := K)) := by
  intro v
  let L := WithLp.fstL 2 ℂ H K
  let R := WithLp.sndL 2 ℂ H K
  refine ⟨WithLp.toLp 2 (L.compLpL 2 μ v, R.compLpL 2 μ v), ?_⟩
  apply Lp.ext
  filter_upwards [pairL2Linear_ae μ (WithLp.toLp 2 (L.compLpL 2 μ v, R.compLpL 2 μ v)),
    L.coeFn_compLpL v, R.coeFn_compLpL v] with q hq hL hR
  change pairL2Linear μ _ q = v q
  rw [hq]
  change WithLp.toLp 2 (L.compLpL 2 μ v q, R.compLpL 2 μ v q) = v q
  rw [hL, hR]
  rfl

/-- L² commutes with the two-component Hilbert sum. -/
def pairL2Equiv : WithLp 2 (Lp H 2 μ × Lp K 2 μ) ≃ₗᵢ[ℂ]
    Lp (WithLp 2 (H × K)) 2 μ :=
  LinearIsometryEquiv.ofSurjective (pairL2Isometry μ) (pairL2Isometry_surjective μ)

variable (U : H ≃ₗᵢ[ℂ] Lp K 2 μ)

/-- Apply the same Gaussian unitary to radiation and potential components. -/
def productUnitary : WithLp 2 (H × H) ≃ₗᵢ[ℂ] Lp (WithLp 2 (K × K)) 2 μ :=
  (U.withLpProdCongr 2 U).trans (pairL2Equiv μ)

theorem productUnitary_ae (u : WithLp 2 (H × H)) :
    productUnitary μ U u =ᵐ[μ] fun q => WithLp.toLp 2 (U u.fst q, U u.snd q) :=
  pairL2Linear_ae μ _

end GptLean.PhysicalGaussianCoordinates
