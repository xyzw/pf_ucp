import PfHk.PauliCarlemanClassical
import PfHk.PauliCarlemanQuantumShift
import PfHk.PauliCarlemanSource

/-! The physical classical and shifted quantum Zeeman estimates imply
the actual quarter-source smallness condition. The generic coupled
absorption lemma then controls the orbital source by the full source. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliPhysicalCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput
  PfHk.PhysicalFieldRegularity PfHk.PhysicalDyadicEnergy PfHk.SmoothCutoffBounds
  PfHk.SmoothDyadicCutoffs PfHk.PauliSpin PfHk.CoordinateSobolev
  PfHk.PauliCarlemanFinite

attribute [local instance] PhysicalLocalExternalCarleman.endpointPhotonRealInner

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

private theorem regroup_smallness {a b c : ℝ} (h : a + b + c ≤ 1 / 8) :
    a + (b + c) ≤ 1 / 8 := by simpa only [add_assoc] using h

variable {N : ℕ} {O₀ : Configuration N} {ρ : ℝ}
attribute [local irreducible] referenceSubspace inclusion
  PauliMagneticClassicalOperator.zeeman PauliCarlemanQuantumShift.shifted
  PauliCarlemanClassical.coefficient PauliCarlemanQuantumShift.radiationCoefficient
  PauliCarlemanQuantumShift.massCoefficient

/-- The physical magnetic bounds supply integrability and a genuine
quarter-source bound before the already proved generic absorption. -/
theorem magnetic_source_absorption
    (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (a : PhysicalLocalExternalCoefficients.Data O₀ ρ)
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    {p : ℝ} (hp : 2 < p)
    (hBp : ∀ n μ, MemLp (B n μ) (ENNReal.ofReal p) volume)
    (hUV : CarlemanUV χ) (E : ℝ)
    {O : Configuration N} {family : BufferedFamily O}
    {R r₀ τ α C₂ C₂e : ℝ} {hR : 0 < R}
    (hτ : 0 < τ) (hα : 0 < α) (h2R : 2 * R ≤ Real.exp (-2))
    (hRr : R ≤ r₀) (hrone : r₀ < 1)
    (u : PauliReference.Ref N)
    (hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s))
    (hcomp : ∀ s, ComparisonDomain (fun _ => 0) (u s))
    (hB : ∀ n μ s, HasMultiplier (coordinateCoefficient n (B n μ))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))
    (g f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hsupp : ∀ s, AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R)
    (he : PauliCarlemanFinite.Estimate F χ C e a spectral family R hR τ α C₂ C₂e u hu g)
    (hmass : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      r ^ (4 : ℝ) / CarlemanWeights.beta α (-Real.log r) ≤ 1)
    (hdyadic : ∀ j, radius R j ^ (4 - 2 * (3 / p)) / dyadicBeta α R j ≤ 1)
    (hop : ∀ s, (fun X => g s X) =ᵐ[volume.restrict (Metric.ball O R)] fun X =>
      f s X - (PauliMagneticClassicalOperator.zeeman B u hB s X +
        PauliCarlemanQuantumShift.shifted F χ C e hUV E u s X))
    (hsmall :
      PauliCarlemanClassical.coefficient S B p 1 (4 * 6144) (4 * C₂) * τ ^ (-(3 - 6 / p)) +
        PauliCarlemanQuantumShift.radiationCoefficient (N := N) F χ e hUV r₀ * τ ^ (-1 : ℝ) +
        PauliCarlemanQuantumShift.massCoefficient (N := N) F χ e hUV E 1 * τ ^ (-3 : ℝ) ≤
          1 / 8) :
    IntegrableOn (sourceEnergySum O τ α f) (Metric.ball O R) ∧
      (∫ X in Metric.ball O R, PauliCarlemanSource.density (centeredSourceWeight O τ α)
        (fun s Y => PauliMagneticClassicalOperator.zeeman B u hB s Y +
          PauliCarlemanQuantumShift.shifted F χ C e hUV E u s Y) X) ≤
        (∫ X in Metric.ball O R, sourceEnergySum O τ α g X) / 4 ∧
      (∫ X in Metric.ball O R, sourceEnergySum O τ α g X) ≤
        4 * ∫ X in Metric.ball O R, sourceEnergySum O τ α f X := by
  have hcl := PauliCarlemanClassical.bound_of_estimate F χ C e a S spectral joint B hp hBp
    h2R hτ hα (by norm_num : (0 : ℝ) ≤ 1) u hu hcomp hB g hsupp he hdyadic
  have hq := PauliCarlemanQuantumShift.source_bound_of_estimate F χ C e a spectral hUV E
    hτ hα hRr hrone (by norm_num : (0 : ℝ) ≤ 1) hmass u hu g he hsupp
  have hsum : (∫ X in Metric.ball O R, sourceEnergySum O τ α g X) =
      ∑ s, ∫ X in Metric.ball O R, sourceEnergy O τ α (g s) X :=
    integral_finsetSum _ (fun s _ => (he.1 s).1)
  have hcl0 : ∀ᵐ X ∂volume, 0 ≤
      ∑ s, sourceEnergy O τ α (PauliMagneticClassicalOperator.zeeman B u hB s) X :=
    ae_of_all _ fun X => Finset.sum_nonneg fun s _ =>
      mul_nonneg (PhysicalSourceAbsorption.centeredSourceWeight_nonneg O τ α X) (sq_nonneg _)
  have hclbound := ((setIntegral_le_integral (s := Metric.ball O R) hcl.1 hcl0).trans hcl.2).trans_eq
    (congrArg (fun x : ℝ =>
      PauliCarlemanClassical.coefficient S B p 1 (4 * 6144) (4 * C₂) *
        τ ^ (-(3 - 6 / p)) * x) hsum.symm)
  have hqbound := hq.2.trans_eq (congrArg (fun x : ℝ =>
      (PauliCarlemanQuantumShift.radiationCoefficient (N := N) F χ e hUV r₀ * τ ^ (-1 : ℝ) +
        PauliCarlemanQuantumShift.massCoefficient (N := N) F χ e hUV E 1 * τ ^ (-3 : ℝ)) * x)
      hsum.symm)
  exact PauliCarlemanSource.absorb_two (μ := volume.restrict (Metric.ball O R))
    (w := centeredSourceWeight O τ α)
    (free := fun s X => g s X) (full := fun s X => f s X)
    (classical := fun s X => PauliMagneticClassicalOperator.zeeman B u hB s X)
    (quantum := fun s X => PauliCarlemanQuantumShift.shifted F χ C e hUV E u s X)
    (ae_of_all _ (PhysicalSourceAbsorption.centeredSourceWeight_nonneg O τ α))
    (PhysicalSourceAbsorption.centeredSourceWeight_measurable O τ α).aestronglyMeasurable.restrict
    (fun s => (Lp.aestronglyMeasurable (g s)).restrict)
    (fun s => (Lp.aestronglyMeasurable (f s)).restrict)
    (fun s => (Lp.aestronglyMeasurable (PauliMagneticClassicalOperator.zeeman B u hB s)).restrict)
    (fun s => (Lp.aestronglyMeasurable
      (PauliCarlemanQuantumShift.shifted F χ C e hUV E u s)).restrict)
    he.2.1 hcl.1.integrableOn hq.1 hop hclbound hqbound (regroup_smallness hsmall)

end PfHk.PauliPhysicalCarleman

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
