import GptLean.PhysicalLocalRellich
import GptLean.PhysicalSectorFourierEnergy

/-!
Compact inclusion of the actual supported local free graph. The only
analytic background is the universal supported fractional Rellich theorem
for Mathlib's Fourier transform. Position support and energy control come
from the concrete Fock and electronic coordinates.
-/

noncomputable section
namespace GptLean.PhysicalLocalCompactness

open MeasureTheory PhysicalFock PhysicalSectorCoordinates PhysicalLocalRellich
  PhotonLocalization
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
set_option Elab.async false

attribute [local irreducible] PhysicalFreeForm.energyOutput

private theorem closedBall_energy_le_one {X : Type*} [NormedAddCommGroup X]
    (u : X) (hu : u ∈ Metric.closedBall (0 : X) 1) :
    ENNReal.ofReal (‖u‖ ^ 2) ≤ 1 := by
  have hn : ‖u‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hu
  have hs : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
  simpa using ENNReal.ofReal_le_ofReal hs

private theorem totallyBounded_image_comp
    {X Y Z : Type*} [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    [NormedSpace ℂ Y] [NormedSpace ℂ Z]
    (f : X → Y) (g : Y →ₗᵢ[ℂ] Z) (h : X → Z) (s : Set X)
    (hf : TotallyBounded (f '' s))
    (he : ∀ x, g (f x) = h x) : TotallyBounded (h '' s) := by
  have hfun : (fun x => g (f x)) = h := funext he
  simpa only [Set.image_image, hfun] using hf.image g.isometry.uniformContinuous

/-- Actual free energy controls each supported sector's fractional Fourier energy. -/
theorem sector_energy_le (N : ℕ) (r : ℝ) (L M : ℕ)
    (u : PhysicalLocalFreeGraph.Domain N r L M) (m : Fin (M + 1)) :
    sectorFourierEnergy
        (Lp.fourierTransformₗᵢ (PhotonSectorPosition N m.val) (Coefficient m.val))
        (sectorHalfSymbol N m.val)
        (sectors N r L M (PhysicalLocalFreeGraph.inclusion N r L M u) m) ≤
      ENNReal.ofReal (‖u‖ ^ 2) := by
  have hcoord := sectors_inclusion N r L M u m
  have he := congrArg (fun v : PhotonSectorL2 N m.val ↥(Coefficient m.val) =>
    sectorFourierEnergy (N := N) (m := m)
      (Lp.fourierTransformₗᵢ (PhotonSectorPosition N m.val) ↥(Coefficient m.val))
      (sectorHalfSymbol N m.val) v) hcoord
  exact he.le.trans (PhysicalSectorCoordinates.half_energy_le N m.val u.val)

/-- The graph unit ball is precompact in the full local support subspace. -/
theorem inclusion_totallyBounded
    (B : PhysicalRellichFourier.StandardSupportedHalfRellich)
    (N : ℕ) (r : ℝ) (L M : ℕ) (hr : 0 ≤ r) :
    TotallyBounded (PhysicalLocalFreeGraph.inclusion N r L M ''
      Metric.closedBall (0 : PhysicalLocalFreeGraph.Domain N r L M) 1) := by
  let C (m : Fin (M + 1)) : Set (PhotonSectorL2 N m.val (Coefficient m.val)) :=
    {u | (∀ᵐ x ∂volume,
        x ∉ sectorConfigurationRegion N m.val ((L : ℝ) + 1) r → u x = 0) ∧
      sectorFourierEnergy
        (Lp.fourierTransformₗᵢ (PhotonSectorPosition N m.val) (Coefficient m.val))
        (sectorHalfSymbol N m.val) u ≤ 1}
  have hC (m : Fin (M + 1)) : IsCompact (C m) := by
    exact B.compact_half_ball (Fin (N + m.val) × Fin 3) (Coefficient m.val)
      (sectorConfigurationRegion N m.val ((L : ℝ) + 1) r)
      (sectorConfigurationRegion_bounded N m.val
        (add_nonneg (Nat.cast_nonneg L) zero_le_one) hr)
  have hprod : IsCompact ((WithLp.toLp 2) '' Set.pi Set.univ C) :=
    (isCompact_univ_pi hC).image (PiLp.continuous_toLp 2 _)
  have hi : sectors N r L M ''
      (PhysicalLocalFreeGraph.inclusion N r L M '' Metric.closedBall 0 1) ⊆
      (WithLp.toLp 2) '' Set.pi Set.univ C := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨fun m => sectors N r L M (PhysicalLocalFreeGraph.inclusion N r L M u) m,
      ?_, rfl⟩
    intro m _
    exact ⟨sectors_supported N r L M _ m, (sector_energy_le N r L M u m).trans
      (@closedBall_energy_le_one (PhysicalLocalFreeGraph.Domain N r L M)
        (PhysicalLocalFreeGraph.domainSubspace N r L M).normedAddCommGroup u hu)⟩
  exact (totallyBounded_image_iff (sectors N r L M).isometry.isUniformInducing).mp
    (hprod.totallyBounded.subset hi)

/-- The same precompact unit ball in the actual coupled wave space. -/
theorem supportValue_totallyBounded
    (B : PhysicalRellichFourier.StandardSupportedHalfRellich)
    (N : ℕ) (r : ℝ) (L M : ℕ) (hr : 0 ≤ r) :
    TotallyBounded (PhysicalLocalFreeGraph.supportValue N r L M ''
      Metric.closedBall (0 : PhysicalLocalFreeGraph.Domain N r L M) 1) := by
  have h := @totallyBounded_image_comp
    (PhysicalLocalFreeGraph.Domain N r L M)
    (PhysicalLocalFreeGraph.Space N r L M)
    (PhysicalFreeForm.WaveSpace (Fin N × Fin 3))
    (PhysicalLocalSupport.localSupport N r L M).normedAddCommGroup inferInstance
    (Submodule.normedSpace (𝕜 := ℂ) (PhysicalLocalSupport.localSupport N r L M)) inferInstance
    (PhysicalLocalFreeGraph.inclusion N r L M)
    (PhysicalLocalFreeGraph.embedding N r L M)
    (PhysicalLocalFreeGraph.supportValue N r L M)
    (Metric.closedBall (0 : PhysicalLocalFreeGraph.Domain N r L M) 1)
    (inclusion_totallyBounded B N r L M hr)
    (fun _ => rfl)
  exact h

end GptLean.PhysicalLocalCompactness
