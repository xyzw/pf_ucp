import PfHk.PauliCarlemanFinite
import PfHk.PauliMixedSeries

/-! The full Pauli estimate retains the physical covariant, radiation
and mass density and both spin-summed fractional series. Source
absorption changes only the universal multiplicative constants. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliPhysicalCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalFieldRegularity
  PfHk.PhysicalDyadicEnergy PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs
  PfHk.PauliSpin PfHk.PauliCarlemanFinite

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

private theorem density_transfer {D F G : ℝ} (hd : D ≤ 520 * F) (hf : F ≤ 4 * G) :
    D ≤ 2080 * G := by linarith only [hd, hf]

variable {N : ℕ} {O₀ : Configuration N} {ρ : ℝ}
attribute [local irreducible] referenceSubspace inclusion

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (a : PhysicalLocalExternalCoefficients.Data O₀ ρ)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))

def Estimate {O : Configuration N} (family : BufferedFamily O)
    (R : ℝ) (hR : 0 < R) (τ α C₂ C₂e : ℝ)
    (u : PauliReference.Ref N)
    (hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s))
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3)) : Prop :=
  IntegrableOn (sourceEnergySum O τ α f) (Metric.ball O R) ∧
    (∀ s, Integrable (PhysicalExternalEnergy.density F χ C e a.vector a.positive a.negative
      O τ α (u s) (hu s))) ∧
    (∫ X, densitySum F χ C e a O τ α u hu X) ≤
      2080 * ∫ X in Metric.ball O R, sourceEnergySum O τ α f X ∧
    PauliMixedSeries.Bound spectral
      (fun s => PhysicalFractionalCarleman.localized family R hR τ α (u s))
      (dyadicBeta α R) (radius R) τ (16 * 6144) (16 * C₂)
      (∫ X in Metric.ball O R, sourceEnergySum O τ α f X) ∧
    PauliMixedSeries.Bound spectral
      (fun s => PhysicalEnlargedFractionalCarleman.localized family R hR τ α (u s))
      (dyadicBeta α R) (radius R) τ (16 * 40960) (16 * C₂e)
      (∫ X in Metric.ball O R, sourceEnergySum O τ α f X)

theorem of_orbital {O : Configuration N} {family : BufferedFamily O}
    {R τ α C₂ C₂e : ℝ} {hR : 0 < R}
    {u : PauliReference.Ref N}
    {hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s)}
    {g f : SpinIndex N → WaveSpace (Fin N × Fin 3)}
    (he : PauliCarlemanFinite.Estimate F χ C e a spectral family R hR τ α C₂ C₂e u hu g)
    (hC₂ : 0 ≤ C₂) (hC₂e : 0 ≤ C₂e)
    (hfull : IntegrableOn (sourceEnergySum O τ α f) (Metric.ball O R))
    (habs : (∫ X in Metric.ball O R, sourceEnergySum O τ α g X) ≤
      4 * ∫ X in Metric.ball O R, sourceEnergySum O τ α f X) :
    Estimate F χ C e a spectral family R hR τ α C₂ C₂e u hu f := by
  have hsum : (∫ X in Metric.ball O R, sourceEnergySum O τ α g X) =
      ∑ s, ∫ X in Metric.ball O R, sourceEnergy O τ α (g s) X :=
    integral_finsetSum _ (fun s _ => (he.1 s).1)
  have hsource : (∑ s, ∫ X in Metric.ball O R, sourceEnergy O τ α (g s) X) ≤
      4 * ∫ X in Metric.ball O R, sourceEnergySum O τ α f X := hsum.symm.le.trans habs
  have hstandard := (PauliMixedSeries.of_components (fun s => (he.1 s).2.2.2.1)).transfer_source
    (by norm_num) (mul_nonneg (by norm_num) hC₂) hsource
  have henlarged := (PauliMixedSeries.of_components (fun s => (he.1 s).2.2.2.2)).transfer_source
    (by norm_num) (mul_nonneg (by norm_num) hC₂e) hsource
  have hstd0 : (4 : ℝ) * (4 * 6144) = 16 * 6144 := by ring
  have hstd2 : (4 : ℝ) * (4 * C₂) = 16 * C₂ := by ring
  have hext0 : (4 : ℝ) * (4 * 40960) = 16 * 40960 := by ring
  have hext2 : (4 : ℝ) * (4 * C₂e) = 16 * C₂e := by ring
  refine ⟨hfull, fun s => (he.1 s).2.1, density_transfer he.2.2.2 habs, ?_, ?_⟩
  · exact (congrArg₂ (fun c₀ c₂ : ℝ => PauliMixedSeries.Bound spectral
      (fun s => PhysicalFractionalCarleman.localized family R hR τ α (u s))
      (dyadicBeta α R) (radius R) τ c₀ c₂
      (∫ X in Metric.ball O R, sourceEnergySum O τ α f X)) hstd0 hstd2).mp hstandard
  · exact (congrArg₂ (fun c₀ c₂ : ℝ => PauliMixedSeries.Bound spectral
      (fun s => PhysicalEnlargedFractionalCarleman.localized family R hR τ α (u s))
      (dyadicBeta α R) (radius R) τ c₀ c₂
      (∫ X in Metric.ball O R, sourceEnergySum O τ α f X)) hext0 hext2).mp henlarged

end PfHk.PauliPhysicalCarleman

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
