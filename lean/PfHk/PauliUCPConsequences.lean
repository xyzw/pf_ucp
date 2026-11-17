import PfHk.PauliUniqueContinuation
import PfHk.PauliUniformCarleman
import PfHk.PauliCurrentGroundState
import PfHk.ExceptionalConfigurationGeometry

/-! Physical spinful unique continuation and spin-summed density
positivity. The Carleman and local-energy inputs are proved internally.
Regularity is required only on the stated open one-body region. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliUCPConsequences

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.PhysicalPairDuality GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PhysicalCommonFormDomain
  PfHk.CenteredPhysicalReference PfHk.UniqueContinuationDensity
  PfHk.ExceptionalConfigurationGeometry PfHk.PauliPhysicalLocalRegularity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] referenceSubspace inclusion PauliReference.wave

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
  (B : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e)

section Open

variable {Ω : Set PhysicalSourceCoordinates.Position} (a : RegularityOn A v Ω)
  (hN : 0 < N) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
  (hfull : ∀ᵐ x : PhysicalSourceCoordinates.Position ∂volume, x ∈ Ω)

include B a hN hΩ hconn hfull

theorem zero_of_infinite_order_on_open {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u))
    {X₀ : Configuration N} (hX₀ : X₀ ∈ configurationDomain Ω N)
    (hflat : InfiniteOrder.FlatAtZero
      (localMass (μ := volume) (PauliReference.wave u) X₀)) :
    ∀ᵐ X ∂volume, PauliReference.wave u X = 0 := by
  exact PauliOperatorCarleman.zero_of_infinite_order F χ C e A v c hc hN
    (PauliOperatorCarleman.uniform_localCarleman F χ C e A v c hc B a hΩ hN
      (1 / 2) (by norm_num) E)
    (by norm_num : (0 : ℝ) < 1 / 2)
    (configurationDomain_isPreconnected hΩ hconn N) (configurationDomain_ae hfull N)
    heigen hX₀ hflat

theorem zero_of_positive_zero_measure_on_open {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u))
    (hpositive : 0 < volume {X | PauliReference.wave u X = 0}) :
    ∀ᵐ X ∂volume, PauliReference.wave u X = 0 := by
  exact PauliOperatorCarleman.zero_of_positive_zero_measure F χ C e A v c hc hN
    (PauliOperatorCarleman.uniform_localCarleman F χ C e A v c hc B a hΩ hN
      (1 / 2) (by norm_num) E)
    (by norm_num : (0 : ℝ) < 1 / 2)
    (configurationDomain_isPreconnected hΩ hconn N) (configurationDomain_ae hfull N)
    heigen hpositive

theorem zero_of_zero_neighborhood_on_open {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u))
    {X₀ : Configuration N} (hX₀ : X₀ ∈ configurationDomain Ω N)
    (hzero : X₀ ∈ UniqueContinuation.zeroNeighborhoods volume (PauliReference.wave u)) :
    ∀ᵐ X ∂volume, PauliReference.wave u X = 0 :=
  zero_of_infinite_order_on_open F χ C e A v c hc B a hN hΩ hconn hfull heigen hX₀
    (UniqueContinuationDensity.flat_of_zeroNeighborhood hzero)

theorem ae_nonzero_on_open {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u)) (hu_ne : u ≠ 0) :
    ∀ᵐ X ∂volume, PauliReference.wave u X ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  by_contra hzero
  have hz := zero_of_positive_zero_measure_on_open F χ C e A v c hc B a hN hΩ hconn hfull heigen
    (bot_lt_iff_ne_bot.mpr hzero)
  exact PauliReference.wave_ne_zero hu_ne (Lp.eq_zero_iff_ae_eq_zero.mpr hz)

theorem ae_norm_pos_on_open {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u)) (hu_ne : u ≠ 0) :
    ∀ᵐ X ∂volume, 0 < ‖PauliReference.wave u X‖ :=
  (ae_nonzero_on_open F χ C e A v c hc B a hN hΩ hconn hfull heigen hu_ne).mono fun _ hX => norm_pos_iff.mpr hX

theorem electronic_density_pos_on_open {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u)) (hu_ne : u ≠ 0) :
    ∀ᵐ x ∂volume, 0 < PauliReference.density u x :=
  PauliReference.density_pos_ae hN u (ae_nonzero_on_open F χ C e A v c hc B a hN hΩ hconn hfull heigen hu_ne)

theorem pair_density_pos_on_open {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u)) (hu_ne : u ≠ 0) :
    ∀ᵐ x ∂volume, 0 < PhysicalPairSpace.densityL1 (data C e F χ u) x :=
  PauliGroundState.data_density_pos_ae C e F χ hN u
    (ae_nonzero_on_open F χ C e A v c hc B a hN hΩ hconn hfull heigen hu_ne)

end Open

section Global

variable (a : RegularityOn A v Set.univ) (hN : 0 < N)

include B a hN

theorem zero_of_infinite_order {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u))
    {X₀ : Configuration N} (hX₀ : X₀ ∈ distinctConfigurations N)
    (hflat : InfiniteOrder.FlatAtZero
      (localMass (μ := volume) (PauliReference.wave u) X₀)) :
    ∀ᵐ X ∂volume, PauliReference.wave u X = 0 :=
  zero_of_infinite_order_on_open F χ C e A v c hc B a hN isOpen_univ isPreconnected_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    heigen ⟨hX₀, fun _ => Set.mem_univ _⟩ hflat

theorem zero_of_positive_zero_measure {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u))
    (hpositive : 0 < volume {X | PauliReference.wave u X = 0}) :
    ∀ᵐ X ∂volume, PauliReference.wave u X = 0 :=
  zero_of_positive_zero_measure_on_open F χ C e A v c hc B a hN isOpen_univ isPreconnected_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) heigen hpositive

theorem zero_of_zero_neighborhood {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u))
    {X₀ : Configuration N} (hX₀ : X₀ ∈ distinctConfigurations N)
    (hzero : X₀ ∈ UniqueContinuation.zeroNeighborhoods volume (PauliReference.wave u)) :
    ∀ᵐ X ∂volume, PauliReference.wave u X = 0 :=
  zero_of_zero_neighborhood_on_open F χ C e A v c hc B a hN isOpen_univ isPreconnected_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    heigen ⟨hX₀, fun _ => Set.mem_univ _⟩ hzero

theorem ae_nonzero {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u)) (hu_ne : u ≠ 0) :
    ∀ᵐ X ∂volume, PauliReference.wave u X ≠ 0 :=
  ae_nonzero_on_open F χ C e A v c hc B a hN isOpen_univ isPreconnected_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) heigen hu_ne

theorem ae_norm_pos {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u)) (hu_ne : u ≠ 0) :
    ∀ᵐ X ∂volume, 0 < ‖PauliReference.wave u X‖ :=
  ae_norm_pos_on_open F χ C e A v c hc B a hN isOpen_univ isPreconnected_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) heigen hu_ne

theorem electronic_density_pos {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u)) (hu_ne : u ≠ 0) :
    ∀ᵐ x ∂volume, 0 < PauliReference.density u x :=
  electronic_density_pos_on_open F χ C e A v c hc B a hN isOpen_univ isPreconnected_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) heigen hu_ne

theorem pair_density_pos {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c)
      (negative v c) E u (physicalDomain A v c hc u)) (hu_ne : u ≠ 0) :
    ∀ᵐ x ∂volume, 0 < PhysicalPairSpace.densityL1 (data C e F χ u) x :=
  pair_density_pos_on_open F χ C e A v c hc B a hN isOpen_univ isPreconnected_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) heigen hu_ne

end Global

end PfHk.PauliUCPConsequences

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
