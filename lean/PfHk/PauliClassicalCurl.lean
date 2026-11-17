import PfHk.PauliClassicalCurlApproximation
import PfHk.SmoothVectorTruncation

/-! Distributional classical curl is a divergence of a rotated vector
field. Smooth localization therefore uses the retained ordinary
Friedrichs theorem without assuming individual weak derivatives of A. -/

noncomputable section
namespace PfHk.PauliClassicalCurl

open MeasureTheory GptLean.PhysicalSourceCoordinates
  PfHk.FriedrichsDivergenceBackground
open scoped ENNReal ContDiff

set_option Elab.async false
set_option maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false

def rotated (i j : Fin 3) (A : Fin 3 → Position → ℝ)
    (k : Fin 3) (x : Position) : ℝ :=
  if k = i then A j x else if k = j then -A i x else 0

/-- The distributional relation b = ∂ᵢ Aⱼ − ∂ⱼ Aᵢ, using real compact
smooth tests supported inside the specified open region. -/
def WeakCurlPairOn (Ω : Set Position) (A : Fin 3 → Position → ℝ)
    (i j : Fin 3) (b : Position → ℝ) : Prop :=
  ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ x, b x * φ x) = (∫ x, A i x * coordinatePartial φ j x) -
      ∫ x, A j x * coordinatePartial φ i x

theorem rotated_test (i j : Fin 3) (hij : i ≠ j)
    (A : Fin 3 → Position → ℝ) (φ : Position → ℝ) :
    -(∑ k : Fin 3, ∫ x, rotated i j A k x * coordinatePartial φ k x) =
      (∫ x, A i x * coordinatePartial φ j x) -
        ∫ x, A j x * coordinatePartial φ i x := by
  have he (k : Fin 3) : (∫ x, rotated i j A k x * coordinatePartial φ k x) =
      (if k = i then ∫ x, A j x * coordinatePartial φ i x else 0) +
      (if k = j then -(∫ x, A i x * coordinatePartial φ j x) else 0) := by
    by_cases hki : k = i
    · subst k
      simp [rotated, hij]
    · by_cases hkj : k = j
      · subst k
        simp [rotated, Ne.symm hij, neg_mul]
        exact integral_neg _
      · simp [rotated, hki, hkj]
  simp only [he, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem weakCurlPairOn_iff (Ω : Set Position) (i j : Fin 3) (hij : i ≠ j)
    (A : Fin 3 → Position → ℝ) (b : Position → ℝ) :
    WeakCurlPairOn Ω A i j b ↔ WeakDivergenceOn Ω (rotated i j A) b := by
  constructor
  · intro h φ hφ hφc hφs
    exact (h φ hφ hφc hφs).trans (rotated_test i j hij A φ).symm
  · intro h φ hφ hφc hφs
    exact (h φ hφ hφc hφs).trans (rotated_test i j hij A φ)

theorem rotated_memLp {ν : Measure Position} {p : ℝ≥0∞}
    (i j : Fin 3) (A : Fin 3 → Position → ℝ)
    (hA : ∀ k, MemLp (A k) p ν) (k : Fin 3) :
    MemLp (rotated i j A k) p ν := by
  unfold rotated
  by_cases hki : k = i
  · simpa only [ite_eq_left hki] using hA j
  · by_cases hkj : k = j
    · simp only [ite_eq_right hki, ite_eq_left hkj]
      change MemLp (-A i) p ν
      exact (hA i).neg
    · simp only [ite_eq_right hki, ite_eq_right hkj]
      exact MemLp.zero'

def localizedVector (o : Position) (ρ : ℝ) (hρ : 0 < ρ)
    (i j : Fin 3) (A : Fin 3 → Position → ℝ) : Fin 3 → Position → ℝ :=
  truncatedVector (SmoothVectorTruncation.cutoff o ρ hρ) (rotated i j A)

def localizedCurl (o : Position) (ρ : ℝ) (hρ : 0 < ρ)
    (i j : Fin 3) (A : Fin 3 → Position → ℝ) (b : Position → ℝ) : Position → ℝ :=
  truncatedDivergence (SmoothVectorTruncation.cutoff o ρ hρ) (rotated i j A) b

theorem localized_vector_memLp (o : Position) {ρ : ℝ} (hρ : 0 < ρ)
    (i j : Fin 3) (A : Fin 3 → Position → ℝ)
    (hA : ∀ k, MemLp (A k) 6 (volume.restrict (Metric.ball o ρ))) (k : Fin 3) :
    MemLp (localizedVector o ρ hρ i j A k) 6 volume :=
  SmoothVectorTruncation.vector_memLp o hρ (rotated i j A) (rotated_memLp i j A hA) k

theorem localized_curl_memLp (o : Position) {ρ p : ℝ} (hρ : 0 < ρ)
    (i j : Fin 3) (A : Fin 3 → Position → ℝ) (b : Position → ℝ)
    (hA : ∀ k, MemLp (A k) 6 (volume.restrict (Metric.ball o ρ)))
    (hb : MemLp b (ENNReal.ofReal p) (volume.restrict (Metric.ball o ρ))) :
    MemLp (localizedCurl o ρ hρ i j A b) (ENNReal.ofReal (min p 6)) volume :=
  SmoothVectorTruncation.divergence_memLp o hρ (rotated i j A) b
    (rotated_memLp i j A hA) hb

theorem localized_weakDivergence (o : Position) {ρ p : ℝ} (hρ : 0 < ρ) (hp : 2 < p)
    (i j : Fin 3) (hij : i ≠ j) (A : Fin 3 → Position → ℝ) (b : Position → ℝ)
    (hA : ∀ k, MemLp (A k) 6 (volume.restrict (Metric.ball o ρ)))
    (hb : MemLp b (ENNReal.ofReal p) (volume.restrict (Metric.ball o ρ)))
    (hcurl : WeakCurlPairOn (Metric.ball o ρ) A i j b) :
    WeakDivergence (localizedVector o ρ hρ i j A) (localizedCurl o ρ hρ i j A b) :=
  SmoothVectorTruncation.weakDivergence_local o hρ hp
    ((weakCurlPairOn_iff _ i j hij A b).mp hcurl) (rotated_memLp i j A hA) hb

theorem localized_vector_eq (o : Position) {ρ : ℝ} (hρ : 0 < ρ)
    (i j : Fin 3) (A : Fin 3 → Position → ℝ) (k : Fin 3) {x : Position}
    (hx : x ∈ Metric.ball o (ρ / 2)) :
    localizedVector o ρ hρ i j A k x = rotated i j A k x :=
  SmoothVectorTruncation.vector_eq o hρ (rotated i j A) k hx

theorem localized_curl_eq (o : Position) {ρ : ℝ} (hρ : 0 < ρ)
    (i j : Fin 3) (A : Fin 3 → Position → ℝ) (b : Position → ℝ) {x : Position}
    (hx : x ∈ Metric.ball o (ρ / 2)) : localizedCurl o ρ hρ i j A b x = b x :=
  SmoothVectorTruncation.divergence_eq o hρ (rotated i j A) b hx

end PfHk.PauliClassicalCurl
