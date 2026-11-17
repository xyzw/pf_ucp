import PfHk.PauliLocalUniqueContinuation
import PfHk.PauliInfiniteOrder
import PfHk.UniqueContinuationFlatSeed

/-! Propagation of local Pauli vanishing on a connected region of full
measure. The local Carleman estimate is an explicit intermediate input
here and is discharged by the physical endpoint modules. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliOperatorCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.PhysicalPairDuality GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PhysicalCommonFormDomain
  PfHk.CenteredPhysicalReference PfHk.UniqueContinuationDensity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] referenceSubspace inclusion PauliReference.wave

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

theorem zero_of_infinite_order (hN : 0 < N) {E α : ℝ} {U : Set (Configuration N)}
    (hCarleman : UniformLocalCarleman F χ C e A v c hc E α U)
    (hα : 0 < α) (hU : IsPreconnected U)
    (hfull : ∀ᵐ X ∂volume, X ∈ U) {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u))
    {X₀ : Configuration N} (hX₀ : X₀ ∈ U)
    (hflat : InfiniteOrder.FlatAtZero
      (localMass (μ := volume) (PauliReference.wave u) X₀)) :
    ∀ᵐ X ∂volume, PauliReference.wave u X = 0 := by
  let : Nonempty (Fin N × Fin 3) := ⟨(⟨0, hN⟩, 0)⟩
  exact UniqueContinuation.ae_zero_of_uniform_flat_seed
    (X := Configuration N) (H := Fiber N PhotonFock) (μ := volume)
    (ψ := PauliReference.wave u)
    (fun X R τ K => CarlemanAt F χ C e A v c hc E X R α τ K)
    hα hU hfull hCarleman
    (fun X R τ K hCar hR hRsmall hK hcoef hxflat =>
      flat_implies_zero_ball F χ C e A v c hc hCar hα hR hRsmall hK hcoef
        heigen hxflat)
    ⟨X₀, hX₀, hflat⟩

theorem zero_of_positive_zero_measure (hN : 0 < N) {E α : ℝ}
    {U : Set (Configuration N)}
    (hCarleman : UniformLocalCarleman F χ C e A v c hc E α U)
    (hα : 0 < α) (hU : IsPreconnected U)
    (hfull : ∀ᵐ X ∂volume, X ∈ U) {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u))
    (hpositive : 0 < volume {X | PauliReference.wave u X = 0}) :
    ∀ᵐ X ∂volume, PauliReference.wave u X = 0 := by
  obtain ⟨X₀, hX₀, _, hflat⟩ := PauliInfiniteOrder.exists_flat_point C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
    e A v c hc heigen hN hfull hpositive
  exact zero_of_infinite_order F χ C e A v c hc hN hCarleman hα hU hfull
    heigen hX₀ hflat

theorem ae_nonzero (hN : 0 < N) {E α : ℝ} {U : Set (Configuration N)}
    (hCarleman : UniformLocalCarleman F χ C e A v c hc E α U)
    (hα : 0 < α) (hU : IsPreconnected U)
    (hfull : ∀ᵐ X ∂volume, X ∈ U) {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u)) (hu_ne : u ≠ 0) :
    ∀ᵐ X ∂volume, PauliReference.wave u X ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  by_contra hzero
  have hz := zero_of_positive_zero_measure F χ C e A v c hc hN hCarleman
    hα hU hfull heigen (bot_lt_iff_ne_bot.mpr hzero)
  exact PauliReference.wave_ne_zero hu_ne (Lp.eq_zero_iff_ae_eq_zero.mpr hz)

end PfHk.PauliOperatorCarleman

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
