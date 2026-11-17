import PfHk.PhysicalMixedSeries
import PfHk.PauliReference

/-! Mixed fractional estimates summed over the finite spin fiber.
Both summability and the common source bound are retained under
absorption, without a factor equal to the number of spin components. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliMixedSeries

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.PhysicalOperatorDomain
  PfHk.PhysicalDyadicIntegralFractional PfHk.DyadicFractional

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

private theorem finite_series_bound {S : Type*} [Fintype S]
    (f : S → ℕ → ℝ) (source : S → ℝ) (K : ℝ)
    (h : ∀ s, Summable (f s) ∧ (∑' j, f s j) ≤ K * source s) :
    Summable (fun j => ∑ s, f s j) ∧
      (∑' j, ∑ s, f s j) ≤ K * ∑ s, source s := by
  have hsum := hasSum_sum (fun s (_ : s ∈ Finset.univ) => (h s).1.hasSum)
  refine ⟨hsum.summable, hsum.tsum_eq.le.trans ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => (h s).2

private theorem transfer_scalar {s C₀ C₂ F G k : ℝ}
    (hs : 0 ≤ s) (hs2 : s ≤ 2) (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂)
    (h : F ≤ k * G) :
    ((s / 2) * C₂ + (1 - s / 2) * C₀) * F ≤
      ((s / 2) * (k * C₂) + (1 - s / 2) * (k * C₀)) * G := by
  have hw : 0 ≤ (s / 2) * C₂ + (1 - s / 2) * C₀ :=
    add_nonneg (mul_nonneg (by linarith only [hs]) hC₂)
      (mul_nonneg (by linarith only [hs2]) hC₀)
  exact (mul_le_mul_of_nonneg_left h hw).trans_eq (by ring)

variable {N : ℕ} {S : Type*} [Fintype S]
attribute [local irreducible] referenceSubspace inclusion

/-- The fractional L2 norm squared is summed over spin before the
infinite dyadic sum. This is the finite Hilbert amplification of L. -/
def Bound (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (u : S → ℕ → Reference (Fin N × Fin 3) (fun _ => 0))
    (β R : ℕ → ℝ) (τ C₀ C₂ source : ℝ) : Prop :=
  ∃ v : S → ℕ → WaveSpace (Fin N × Fin 3),
    ∃ hv : ∀ s j, IsComparisonPair (fun _ => 0) (u s j) (v s j),
    ∀ a : ℝ, 0 ≤ a → a ≤ 2 →
      Summable (fun j => ∑ s, coefficient τ (β j) (R j) a *
        fractionalNormSq spectral a (u s j) ⟨v s j, hv s j⟩) ∧
      (∑' j, ∑ s, coefficient τ (β j) (R j) a *
        fractionalNormSq spectral a (u s j) ⟨v s j, hv s j⟩) ≤
        ((a / 2) * C₂ + (1 - a / 2) * C₀) * source

theorem of_components
    {spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3)}
    {u : S → ℕ → Reference (Fin N × Fin 3) (fun _ => 0)}
    {β R : ℕ → ℝ} {τ C₀ C₂ : ℝ} {source : S → ℝ}
    (h : ∀ s, PhysicalMixedSeries.Bound spectral (u s) β R τ C₀ C₂ (source s)) :
    Bound spectral u β R τ C₀ C₂ (∑ s, source s) := by
  let v := fun s => Classical.choose (h s)
  let hv := fun s => Classical.choose (Classical.choose_spec (h s))
  have hseries := fun s => Classical.choose_spec (Classical.choose_spec (h s))
  refine ⟨v, hv, ?_⟩
  intro a ha ha2
  exact finite_series_bound _ source _ (fun s => hseries s a ha ha2)

theorem Bound.transfer_source
    {spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3)}
    {u : S → ℕ → Reference (Fin N × Fin 3) (fun _ => 0)}
    {β R : ℕ → ℝ} {τ C₀ C₂ F G k : ℝ}
    (h : Bound spectral u β R τ C₀ C₂ F)
    (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂) (hsource : F ≤ k * G) :
    Bound spectral u β R τ (k * C₀) (k * C₂) G := by
  let v := Classical.choose h
  let hv := Classical.choose (Classical.choose_spec h)
  have hs := Classical.choose_spec (Classical.choose_spec h)
  refine ⟨v, hv, ?_⟩
  intro a ha ha2
  exact ⟨(hs a ha ha2).1,
    (hs a ha ha2).2.trans (transfer_scalar ha ha2 hC₀ hC₂ hsource)⟩

end PfHk.PauliMixedSeries

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
