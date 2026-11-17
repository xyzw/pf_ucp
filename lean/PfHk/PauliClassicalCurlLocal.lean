import PfHk.PauliClassicalCurl


/-! Local rough-curl forms on compactly supported reference vectors.
Cutoff transport needs support of the wave functions only. -/

noncomputable section
namespace PfHk.PauliClassicalCurl

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.ElectronicH1Space PfHk.CoordinateSobolev PfHk.PauliClassicalCurlForm
  PfHk.PhysicalOperatorDomain PfHk.FriedrichsDivergenceBackground
open scoped ENNReal Topology InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 15000

section Support

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def SupportedInCoordinate (n : Fin N) (s : Set GptLean.PhysicalSourceCoordinates.Position)
    (u : L2 H (Fin N × Fin 3)) : Prop :=
  ∀ᵐ X ∂volume, (GptLean.PhysicalSourceCoordinates.split n X).1 ∉ s → u X = 0


theorem coefficient_product_congr (n : Fin N)
    (s : Set GptLean.PhysicalSourceCoordinates.Position)
    (c d : GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (hcd : ∀ x ∈ s, c x = d x) (u : L2 H (Fin N × Fin 3))
    (hu : SupportedInCoordinate n s u) :
    (fun X => coordinateCoefficient n c X • u X) =ᵐ[volume]
      fun X => coordinateCoefficient n d X • u X := by
  filter_upwards [hu] with X hX
  by_cases hx : (GptLean.PhysicalSourceCoordinates.split n X).1 ∈ s
  · exact congrArg (fun r : ℝ => r • u X) (hcd _ hx)
  · simp only [hX hx, smul_zero]


theorem weightedInner_congr (n : Fin N)
    (s : Set GptLean.PhysicalSourceCoordinates.Position)
    (c d : GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (hcd : ∀ x ∈ s, c x = d x) (u v : L2 H (Fin N × Fin 3))
    (hu : SupportedInCoordinate n s u) :
    weightedInner (coordinateCoefficient n c) v u =ᵐ[volume]
      weightedInner (coordinateCoefficient n d) v u := by
  filter_upwards [hu] with X hX
  by_cases hx : (GptLean.PhysicalSourceCoordinates.split n X).1 ∈ s
  · exact congrArg (fun r : ℝ => (r : ℂ) * inner ℂ (v X) (u X)) (hcd _ hx)
  · simp only [weightedInner, hX hx, inner_zero_right, mul_zero]


theorem pairing_congr (n : Fin N)
    (s : Set GptLean.PhysicalSourceCoordinates.Position)
    (c d : GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (hcd : ∀ x ∈ s, c x = d x) (u v : L2 H (Fin N × Fin 3))
    (hu : SupportedInCoordinate n s u) : pairing n c v u = pairing n d v u :=
  integral_congr_ae (weightedInner_congr n s c d hcd u v hu)


end Support

section GenericLocal

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem local_pairing_integrable_of_bessel
    (S : CoordinateSobolev.Data H N)
    (n : Fin N) (o : GptLean.PhysicalSourceCoordinates.Position)
    {ρ p : ℝ} (hρ : 0 < ρ) (hp : 2 < p)
    (a b : Fin 3) (A : Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (curl : GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (hA : ∀ j, MemLp (A j) 6 (volume.restrict (Metric.ball o ρ)))
    (hcurl : MemLp curl (ENNReal.ofReal p) (volume.restrict (Metric.ball o ρ)))
    (u z uB zB : L2 H (Fin N × Fin 3))
    (huB : BesselPair n (3 / (2 * min p 6)) u uB)
    (hzB : BesselPair n (3 / (2 * min p 6)) z zB)
    (hu : SupportedInCoordinate n (Metric.ball o (ρ / 2)) u) :
    Integrable (weightedInner (coordinateCoefficient n curl) z u) volume := by
  have hq : 2 < min p 6 := SmoothVectorTruncation.divergence_exponent hp
  have ht := (coordinate_bound (H := H) (N := N) S hq n (localizedCurl o ρ hρ a b A curl)
    (localized_curl_memLp o hρ a b A curl hA hcurl) z u zB uB hzB huB).1
  exact ht.congr (weightedInner_congr n (Metric.ball o (ρ / 2))
    (localizedCurl o ρ hρ a b A curl) curl
    (fun x hx => localized_curl_eq o hρ a b A curl hx) u z hu)

end GenericLocal


section Physical

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] PhysicalPFReference.referenceSubspace inclusion

variable {N : ℕ}

set_option maxHeartbeats 50000 in
theorem local_pairing_integrable
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (n : Fin N) (o : GptLean.PhysicalSourceCoordinates.Position)
    {ρ p : ℝ} (hρ : 0 < ρ) (hp : 2 < p)
    (a b : Fin 3) (A : Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (curl : GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (hA : ∀ j, MemLp (A j) 6 (volume.restrict (Metric.ball o ρ)))
    (hcurl : MemLp curl (ENNReal.ofReal p) (volume.restrict (Metric.ball o ρ)))
    (u z : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : SupportedInCoordinate (H := PhotonFock) (N := N) n (Metric.ball o (ρ / 2))
      (inclusion (Fin N × Fin 3) (fun _ => 0) u)) :
    Integrable (weightedInner (H := PhotonFock) (coordinateCoefficient n curl)
      (inclusion (Fin N × Fin 3) (fun _ => 0) z)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u)) volume := by
  have hq : 2 < min p 6 := SmoothVectorTruncation.divergence_exponent hp
  have hq0 : 0 < min p 6 := by linarith
  have hs0 : 0 ≤ 3 / (2 * min p 6) := by positivity
  have hs1 : 3 / (2 * min p 6) ≤ 1 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hU : ∃ uB : WaveSpace (Fin N × Fin 3),
      BesselPair (H := PhotonFock) n (3 / (2 * min p 6))
        (inclusion (Fin N × Fin 3) (fun _ => 0) u) uB ∧
        ‖uB‖ ≤ ‖spectral.root u‖ :=
    @CoordinateComparisonSpectral.Data.form_value N spectral joint n
      (3 / (2 * min p 6)) hs0 hs1 u
  have hZ : ∃ zB : WaveSpace (Fin N × Fin 3),
      BesselPair (H := PhotonFock) n (3 / (2 * min p 6))
        (inclusion (Fin N × Fin 3) (fun _ => 0) z) zB ∧
        ‖zB‖ ≤ ‖spectral.root z‖ :=
    @CoordinateComparisonSpectral.Data.form_value N spectral joint n
      (3 / (2 * min p 6)) hs0 hs1 z
  obtain ⟨uB, huB, _⟩ := hU
  obtain ⟨zB, hzB, _⟩ := hZ
  exact local_pairing_integrable_of_bessel (H := PhotonFock) (N := N)
    S n o hρ hp a b A curl hA hcurl
    (inclusion (Fin N × Fin 3) (fun _ => 0) u)
    (inclusion (Fin N × Fin 3) (fun _ => 0) z)
    uB zB huB hzB hu


end Physical

end PfHk.PauliClassicalCurl

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
