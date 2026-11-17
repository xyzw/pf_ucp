import PfHk.PauliMagneticClassicalOperator
import PfHk.PauliCarlemanFinite
import PfHk.PauliCarlemanRadii

/-! The actual classical Zeeman source has a decaying coefficient relative
to the summed orbital source. Its weighted integrability and every scalar
multiplier are supplied by the proved coordinate estimate. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliCarlemanClassical

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain
  PfHk.PhysicalCarlemanInput PfHk.SmoothDyadicCutoffs PfHk.SmoothCutoffBounds
  PfHk.CoordinateSobolev PfHk.PhysicalDyadicEnergy
  PfHk.PauliMagneticClassicalOperator

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

private theorem interpolation_nonneg {p C₀ C₂ : ℝ} (hp : 2 < p)
    (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂) :
    0 ≤ ((3 / p) / 2) * C₂ + (1 - (3 / p) / 2) * C₀ := by
  have hp0 : 0 < p := by linarith only [hp]
  have hsp : 0 ≤ 3 / p := by positivity
  have hs2 : 3 / p ≤ 2 := (div_le_iff₀ hp0).mpr (by linarith only [hp])
  exact add_nonneg (mul_nonneg (by positivity) hC₂)
    (mul_nonneg (by linarith only [hs2]) hC₀)

private theorem scalar_factor {J K : Type*} [Fintype J] [Fintype K]
    (c : ℝ) (a : J → K → ℝ) (t m f : ℝ) :
    c * (∑ j, ∑ k, a j k * t * m) * f =
      (c * ∑ j, ∑ k, a j k * m) * t * f := by
  simp only [← Finset.sum_mul]
  ring

variable {N : ℕ}
attribute [local irreducible] inclusion referenceSubspace roughMultiply zeeman
  IsComparisonPair PhysicalMixedSeries.Bound PhysicalFractionalCarleman.localized
  PhysicalCoordinateMultipliers.coefficientNormSq

/-- The actual Lp norms and orbital mixed constants determine the
classical coefficient before the Carleman parameter is chosen. -/
def coefficient (S : CoordinateSobolev.Data PhotonFock N)
    (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (p σ C₀ C₂ : ℝ) : ℝ :=
  ((N : ℝ) / 4) * ∑ n, ∑ μ : Fin 3,
    12 * PhysicalCoordinateMultipliers.coefficientNormSq S p (B n μ) * σ *
      (((3 / p) / 2) * C₂ + (1 - (3 / p) / 2) * C₀)

theorem coefficient_nonneg (S : CoordinateSobolev.Data PhotonFock N)
    (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    {p σ C₀ C₂ : ℝ} (hp : 2 < p) (hσ : 0 ≤ σ)
    (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂) : 0 ≤ coefficient S B p σ C₀ C₂ := by
  unfold coefficient
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro n _
  apply Finset.sum_nonneg
  intro μ _
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num)
      (PhysicalCoordinateMultipliers.coefficientNormSq_nonneg S p (B n μ))) hσ)
    (interpolation_nonneg hp hC₀ hC₂)

/-- The source estimate uses any supplied witnesses for the already
derived magnetic products. Proof irrelevance identifies these products
with those constructed by the coordinate multiplier theorem. -/
theorem bound_of_mixed
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    {p : ℝ} (hp : 2 < p)
    (hBp : ∀ n μ, MemLp (B n μ) (ENNReal.ofReal p) volume)
    {O : Configuration N} (family : BufferedFamily O)
    {R τ α σ C₀ C₂ : ℝ} (source : SpinIndex N → ℝ)
    (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2)) (hτ : 0 < τ)
    (hα : 0 < α) (hσ : 0 ≤ σ)
    (u : PauliReference.Ref N)
    (hu : ∀ s, ComparisonDomain (fun _ => 0) (u s))
    (hB : ∀ n μ s, HasMultiplier (coordinateCoefficient n (B n μ))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))
    (hsupp : ∀ s, AnnularSupport
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R)
    (hmixed : ∀ s, PhysicalMixedSeries.Bound spectral
      (PhysicalFractionalCarleman.localized family R hR τ α (u s))
      (dyadicBeta α R) (radius R) τ C₀ C₂ (source s))
    (hratio : ∀ j, radius R j ^ (4 - 2 * (3 / p)) / dyadicBeta α R j ≤ σ) :
    Integrable (fun X => ∑ s, sourceEnergy O τ α (zeeman B u hB s) X) ∧
      (∫ X, ∑ s, sourceEnergy O τ α (zeeman B u hB s) X) ≤
        coefficient S B p σ C₀ C₂ * τ ^ (-(3 - 6 / p)) * ∑ s, source s := by
  have hex := physical_bound (B := B) (u := u) S spectral joint hp hBp family source
    hR hsmall hτ hα hσ hu hsupp hmixed hratio
  have h := Classical.choose_spec hex
  refine ⟨h.1, h.2.trans_eq ?_⟩
  have hexp : -(3 - 2 * (3 / p)) = -(3 - 6 / p) := by ring
  unfold coefficient
  rw [hexp]
  exact scalar_factor ((N : ℝ) / 4)
    (fun n μ => 12 * PhysicalCoordinateMultipliers.coefficientNormSq S p (B n μ) * σ)
    (τ ^ (-(3 - 6 / p))) (((3 / p) / 2) * C₂ + (1 - (3 / p) / 2) * C₀)
    (∑ s, source s)

/-- Specialization to the proved finite-spin orbital external estimate.
No weighted magnetic integrability or smallness is assumed. -/
theorem bound_of_estimate
    {O₀ : Configuration N} {ρ : ℝ}
    (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (a : PhysicalLocalExternalCoefficients.Data O₀ ρ)
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    {p : ℝ} (hp : 2 < p)
    (hBp : ∀ n μ, MemLp (B n μ) (ENNReal.ofReal p) volume)
    {O : Configuration N} {family : BufferedFamily O}
    {R τ α σ C₂ C₂e : ℝ} {hR : 0 < R}
    (hsmall : 2 * R ≤ Real.exp (-2)) (hτ : 0 < τ) (hα : 0 < α) (hσ : 0 ≤ σ)
    (u : PauliReference.Ref N)
    (hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s))
    (hcomp : ∀ s, ComparisonDomain (fun _ => 0) (u s))
    (hB : ∀ n μ s, HasMultiplier (coordinateCoefficient n (B n μ))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hsupp : ∀ s, AnnularSupport
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R)
    (he : PauliCarlemanFinite.Estimate F χ C e a spectral
      family R hR τ α C₂ C₂e u hu f)
    (hratio : ∀ j, radius R j ^ (4 - 2 * (3 / p)) / dyadicBeta α R j ≤ σ) :
    Integrable (fun X => ∑ s, sourceEnergy O τ α (zeeman B u hB s) X) ∧
      (∫ X, ∑ s, sourceEnergy O τ α (zeeman B u hB s) X) ≤
        coefficient S B p σ (4 * 6144) (4 * C₂) * τ ^ (-(3 - 6 / p)) *
          ∑ s, ∫ X in Metric.ball O R, sourceEnergy O τ α (f s) X := by
  have hmixed (s : SpinIndex N) : PhysicalMixedSeries.Bound spectral
      (PhysicalFractionalCarleman.localized family R hR τ α (u s))
      (dyadicBeta α R) (radius R) τ (4 * 6144) (4 * C₂)
      (∫ X in Metric.ball O R, sourceEnergy O τ α (f s) X) := by
    have hs : PhysicalLocalExternalCarleman.Estimate F χ C e a spectral
        family R hR τ α C₂ C₂e (u s) (hu s) (f s) := he.1 s
    exact hs.2.2.2.1
  exact bound_of_mixed S spectral joint B hp hBp family
    (fun s => ∫ X in Metric.ball O R, sourceEnergy O τ α (f s) X)
    hR hsmall hτ hα hσ u hcomp hB hsupp hmixed hratio

end PfHk.PauliCarlemanClassical

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
