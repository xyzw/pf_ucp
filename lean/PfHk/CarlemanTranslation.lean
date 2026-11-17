import PfHk.CarlemanSpatialDensity
import Mathlib.MeasureTheory.Group.Integral

/-! Ordinary electronic translation of the physical Carleman densities
and their spatial ball integrals. -/

noncomputable section
namespace PfHk.CarlemanSpatialDensity

open MeasureTheory Set PfHk.PolarCalculus PfHk.CarlemanWeights
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type*} [Fintype I] [DecidableEq I]

def centeredDensity (O : Position I) (τ α : ℝ) (M D R : Position I → ℝ) (X : Position I) : ℝ :=
  Real.exp (2*τ*weight α (-Real.log (dist X O))) *
    (τ^3*beta α (-Real.log (dist X O))*(dist X O^2)⁻¹*M X +
      τ*beta α (-Real.log (dist X O))*D X + 2*τ*R X)

def centeredSource (O : Position I) (τ α : ℝ) (S : Position I → ℝ) (X : Position I) : ℝ :=
  Real.exp (2*τ*weight α (-Real.log (dist X O))) * dist X O^2*S X

theorem dist_add_center (O X : Position I) : dist (O+X) O = ‖X‖ := by
  rw [dist_eq_norm, add_sub_cancel_left]

theorem centeredDensity_add (O : Position I) (τ α : ℝ) (M D R : Position I → ℝ) (X : Position I) :
    centeredDensity O τ α M D R (O+X) =
      density τ α (fun Y => M (O+Y)) (fun Y => D (O+Y)) (fun Y => R (O+Y)) X := by
  unfold centeredDensity density
  rw [dist_add_center]

theorem centeredSource_add (O : Position I) (τ α : ℝ) (S : Position I → ℝ) (X : Position I) :
    centeredSource O τ α S (O+X) = source τ α (fun Y => S (O+Y)) X := by
  unfold centeredSource source
  rw [dist_add_center]

theorem integral_ball_add_left (O : Position I) (R : ℝ) (f : Position I → ℝ) :
    (∫ X in Metric.ball 0 R, f (O+X)) = ∫ X in Metric.ball O R, f X := by
  have hset : (fun X : Position I => O+X) ⁻¹' Metric.ball O R = Metric.ball 0 R := by
    ext X
    simp only [mem_preimage, Metric.mem_ball, dist_add_center, dist_zero_right]
  have h := (measurePreserving_add_left volume O).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft O).measurableEmbedding f (Metric.ball O R)
  simpa only [hset] using h

theorem integral_centeredDensity (O : Position I) (R τ α : ℝ) (M D Q : Position I → ℝ) :
    (∫ X in Metric.ball 0 R,
      density τ α (fun Y => M (O+Y)) (fun Y => D (O+Y)) (fun Y => Q (O+Y)) X) =
      ∫ X in Metric.ball O R, centeredDensity O τ α M D Q X := by
  rw [← integral_ball_add_left O R (centeredDensity O τ α M D Q)]
  exact integral_congr_ae (ae_of_all _ fun X => (centeredDensity_add O τ α M D Q X).symm)

theorem integral_centeredSource (O : Position I) (R τ α : ℝ) (S : Position I → ℝ) :
    (∫ X in Metric.ball 0 R, source τ α (fun Y => S (O+Y)) X) =
      ∫ X in Metric.ball O R, centeredSource O τ α S X := by
  rw [← integral_ball_add_left O R (centeredSource O τ α S)]
  exact integral_congr_ae (ae_of_all _ fun X => (centeredSource_add O τ α S X).symm)

end PfHk.CarlemanSpatialDensity
