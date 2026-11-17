import PfHk.CoordinateMultiplication
import PfHk.PhysicalLocalEnergyRough

/-! Local coordinate coefficients can be extended by zero for multiplier
estimates. The selected coordinate is a contraction of configuration space,
so the original and extended multiplication agree on a configuration ball.
This module makes no assertion about the distributional divergence of a
zero-extended vector field. -/

noncomputable section
namespace PfHk.CoordinateCoefficientLocalization

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.PhysicalSourceCoordinates PfHk.CoordinateSobolev PfHk.PhysicalLocalEnergy
open scoped ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option maxHeartbeats 20000

variable {N : ℕ}

local instance localizedPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

theorem scalar_smul_eq_of_eq_or_zero {H : Type*} [Zero H] [SMulZeroClass ℝ H]
    (a b : ℝ) (v : H) (h : a = b ∨ v = 0) : a • v = b • v := by
  rcases h with h | h
  · exact congrArg (fun c : ℝ => c • v) h
  · simp only [h, smul_zero]

theorem coordinate_dist_le (n : Fin N) (x y : Configuration N) :
    dist (split n x).1 (split n y).1 ≤ dist x y := by
  let P := PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2
    (fun _ : Fin 3 ⊕ Remaining n => ℝ)
  have h := WithLp.dist_fst_le (P (reindex n x)) (P (reindex n y))
  change dist (split n x).1 (split n y).1 ≤ dist (P (reindex n x)) (P (reindex n y)) at h
  simpa only [P.dist_map, (reindex n).dist_map] using h

def zeroExtension (o : Position) (ρ : ℝ) (b : Position → ℝ) : Position → ℝ :=
  (Metric.ball o ρ).indicator b

theorem zeroExtension_memLp {q : ℝ≥0∞} (o : Position) (ρ : ℝ) (b : Position → ℝ)
    (hb : MemLp b q (volume.restrict (Metric.ball o ρ))) :
    MemLp (zeroExtension o ρ b) q volume :=
  (memLp_indicator_iff_restrict measurableSet_ball).mpr hb

theorem zeroExtension_lpNorm (q : ℝ≥0∞) (o : Position) (ρ : ℝ) (b : Position → ℝ) :
    eLpNorm (zeroExtension o ρ b) q volume =
      eLpNorm b q (volume.restrict (Metric.ball o ρ)) :=
  eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball

theorem coordinate_zeroExtension_eq (n : Fin N) (O x : Configuration N)
    (ρ : ℝ) (b : Position → ℝ) (hx : x ∈ Metric.ball O ρ) :
    coordinateCoefficient n (zeroExtension (split n O).1 ρ b) x =
      coordinateCoefficient n b x := by
  have hp : (split n x).1 ∈ Metric.ball (split n O).1 ρ :=
    (coordinate_dist_le n x O).trans_lt hx
  exact Set.indicator_of_mem hp b

theorem zeroExtension_product_ae (n : Fin N) (O : Configuration N) (ρ : ℝ)
    (b : Position → ℝ) (u : WaveSpace (Fin N × Fin 3))
    (hu : ∀ᵐ x ∂volume, x ∉ Metric.ball O ρ → u x = 0) :
    (fun x => coordinateCoefficient n (zeroExtension (split n O).1 ρ b) x • u x) =ᵐ[volume]
      (fun x => coordinateCoefficient n b x • u x) := by
  filter_upwards [hu] with x hx
  exact scalar_smul_eq_of_eq_or_zero (H := PhotonFock) _ _ (u x) (by
    by_cases hball : x ∈ Metric.ball O ρ
    · exact Or.inl (coordinate_zeroExtension_eq n O x ρ b hball)
    · exact Or.inr (hx hball))

theorem hasMultiplier_of_zeroExtension (n : Fin N) (O : Configuration N) (ρ : ℝ)
    (b : Position → ℝ) (u : WaveSpace (Fin N × Fin 3))
    (hu : ∀ᵐ x ∂volume, x ∉ Metric.ball O ρ → u x = 0)
    (hb : HasMultiplier (coordinateCoefficient n (zeroExtension (split n O).1 ρ b)) u) :
    HasMultiplier (coordinateCoefficient n b) u :=
  hb.ae_eq (zeroExtension_product_ae n O ρ b u hu)

theorem roughMultiply_zeroExtension (n : Fin N) (O : Configuration N) (ρ : ℝ)
    (b : Position → ℝ) (u : WaveSpace (Fin N × Fin 3))
    (hu : ∀ᵐ x ∂volume, x ∉ Metric.ball O ρ → u x = 0)
    (hb : HasMultiplier (coordinateCoefficient n (zeroExtension (split n O).1 ρ b)) u)
    (hb' : HasMultiplier (coordinateCoefficient n b) u) :
    roughMultiply (coordinateCoefficient n (zeroExtension (split n O).1 ρ b)) u hb =
      roughMultiply (coordinateCoefficient n b) u hb' := by
  apply Lp.ext
  exact (roughMultiply_ae _ u hb).trans
    ((zeroExtension_product_ae n O ρ b u hu).trans (roughMultiply_ae _ u hb').symm)

end PfHk.CoordinateCoefficientLocalization
