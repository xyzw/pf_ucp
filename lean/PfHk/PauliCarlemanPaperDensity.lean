import PfHk.PauliCarlemanEstimate

/-! The full Pauli estimate gives the displayed covariant Carleman
density on the target ball. The finite spin sum preserves the physical
source constant and the stronger radiation term with coefficient 2 tau. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliPhysicalCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalFieldRegularity
  PfHk.PhysicalDyadicEnergy PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs
  PfHk.PhysicalCarlemanInput PfHk.PauliSpin PfHk.PauliCarlemanFinite

attribute [local instance] PhysicalLocalExternalCarleman.endpointPhotonRealInner

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

private theorem sum_integral_transfer {X S : Type*} [MeasurableSpace X] [Fintype S]
    (μ : Measure X) (U : Set X) (d p : S → X → ℝ) (bound : ℝ)
    (hd : ∀ s, Integrable (d s) μ)
    (hp : ∀ s, IntegrableOn (p s) U μ ∧ (∫ x in U, p s x ∂μ) ≤ ∫ x, d s x ∂μ)
    (hb : (∫ x, ∑ s, d s x ∂μ) ≤ bound) :
    IntegrableOn (fun x => ∑ s, p s x) U μ ∧
      (∫ x in U, ∑ s, p s x ∂μ) ≤ bound := by
  have hi := integrable_finsetSum Finset.univ (fun s _ => (hp s).1)
  have hlocal := integral_finsetSum Finset.univ (fun s _ => (hp s).1)
  have hglobal := integral_finsetSum Finset.univ (fun s _ => hd s)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ => (hp s).2)
  exact ⟨hi, hlocal.le.trans (hsum.trans (hglobal.symm.le.trans hb))⟩

variable {N : ℕ} {O₀ : Configuration N} {ρ : ℝ}
attribute [local irreducible] referenceSubspace inclusion

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (a : PhysicalLocalExternalCoefficients.Data O₀ ρ)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))

def paperDensitySum (O : Configuration N) (τ α : ℝ) (u : PauliReference.Ref N)
    (hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s))
    (X : Configuration N) : ℝ :=
  ∑ s, PhysicalExternalDensityLocality.untruncatedDensity F χ C e
    a.vector a.positive a.negative O τ α (u s) (hu s) X

/-- The physical mass, covariant kinetic and radiation energies satisfy
the paper's spin-summed estimate with the full Pauli source. -/
theorem Estimate.paper_density {O : Configuration N} {family : BufferedFamily O}
    {R τ α C₂ C₂e : ℝ} {hR : 0 < R}
    {u : PauliReference.Ref N}
    {hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s)}
    {f : SpinIndex N → WaveSpace (Fin N × Fin 3)}
    (he : Estimate F χ C e a spectral family R hR τ α C₂ C₂e u hu f)
    (hτ : 0 ≤ τ) (hα : 0 < α) (hRone : R < 1)
    (hsupp : ∀ s, AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R) :
    IntegrableOn (paperDensitySum F χ C e a O τ α u hu) (Metric.ball O R) ∧
      (∫ X in Metric.ball O R, paperDensitySum F χ C e a O τ α u hu X) ≤
        2080 * ∫ X in Metric.ball O R, sourceEnergySum O τ α f X := by
  have hp (s : SpinIndex N) := PhysicalExternalDensityLocality.paper_density_bound
    F χ C e a.vector a.positive a.negative (K := 1)
    (source := ∫ X, PhysicalExternalEnergy.density F χ C e a.vector a.positive a.negative
      O τ α (u s) (hu s) X)
    hτ hα hRone (u s) (hu s) (hsupp s) (he.2.1 s) (one_mul _).symm.le
  exact sum_integral_transfer volume (Metric.ball O R)
    (fun s => PhysicalExternalEnergy.density F χ C e a.vector a.positive a.negative
      O τ α (u s) (hu s))
    (fun s => PhysicalExternalDensityLocality.untruncatedDensity F χ C e
      a.vector a.positive a.negative O τ α (u s) (hu s)) _ he.2.1
    (fun s => ⟨(hp s).1, (hp s).2.trans_eq (one_mul _)⟩) he.2.2.1

end PfHk.PauliPhysicalCarleman

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
