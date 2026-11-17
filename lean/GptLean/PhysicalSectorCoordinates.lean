import GptLean.PhysicalSectorMeasures
import GptLean.PhysicalFiniteSectorCoordinates
import GptLean.PhysicalSourceFubiniEquiv
import Mathlib.Analysis.Fourier.LpSpace

/-!
Concrete position-space sector coordinates on the physical spatial Fock
space. Product-measure regrouping separates finite polarization fibers,
L2 Fubini combines the electronic and photon positions, and the actual
L2 inverse Fourier transform changes each photon momentum sector to
position coordinates. Every map is an isometry constructed here.
-/

noncomputable section

namespace GptLean.PhysicalSectorCoordinates

open MeasureTheory PhysicalFock PhysicalSectorMeasures
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

abbrev Coefficient (m : ℕ) := Lp ℂ 2 (Measure.count : Measure (Polarization m))

private def coefficientEval (m : ℕ) : Coefficient m →ₗ[ℂ] (Polarization m → ℂ) where
  toFun u := u
  map_add' u v := funext (Measure.ae_count_iff.mp (Lp.coeFn_add u v))
  map_smul' c u := funext (Measure.ae_count_iff.mp (Lp.coeFn_smul c u))

instance coefficientFiniteDimensional (m : ℕ) : FiniteDimensional ℂ (Coefficient m) := by
  apply FiniteDimensional.of_injective (coefficientEval m)
  intro u v h
  exact Lp.ext (ae_of_all _ fun x => congrFun h x)

instance coefficientProperSpace (m : ℕ) : ProperSpace (Coefficient m) :=
  FiniteDimensional.proper ℂ (Coefficient m)

section Lift
variable {X H K : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

def liftIsometry (U : H →ₗᵢ[ℂ] K) : Lp H 2 μ →ₗᵢ[ℂ] Lp K 2 μ where
  toLinearMap := (U.toContinuousLinearMap.compLpL 2 μ).toLinearMap
  norm_map' u := by
    change ‖U.toContinuousLinearMap.compLpL 2 μ u‖ = ‖u‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
    filter_upwards [U.toContinuousLinearMap.coeFn_compLpL u] with x hx
    rw [hx]
    exact U.norm_map _

theorem liftIsometry_ae (U : H →ₗᵢ[ℂ] K) (u : Lp H 2 μ) :
    liftIsometry μ U u =ᵐ[μ] fun x => U (u x) := U.toContinuousLinearMap.coeFn_compLpL u
end Lift

/-- The full momentum sector as a polarization-valued function of photon momenta. -/
def fullMomentum (m : ℕ) : FullSector photonMeasure m →ₗᵢ[ℂ]
    Lp (Coefficient m) 2 (volume : Measure (Configuration m)) :=
  PhysicalSourceFubini.curryEquiv.toLinearIsometry.comp
    (Lp.compMeasurePreservingₗᵢ ℂ (modeEquiv m).symm (mode_measurePreserving m).symm)

theorem fullMomentum_represents_ae (m : ℕ) (u : FullSector photonMeasure m) :
    ∀ᵐ k ∂volume, ∀ p : Polarization m,
      fullMomentum m u k p = u ((modeEquiv m).symm (k, p)) := by
  let q := Lp.compMeasurePreservingₗᵢ ℂ (modeEquiv m).symm
    (mode_measurePreserving m).symm u
  have hq : q =ᵐ[(volume : Measure (Configuration m)).prod Measure.count]
      fun z => u ((modeEquiv m).symm z) :=
    Lp.coeFn_compMeasurePreserving u (mode_measurePreserving m).symm
  filter_upwards [PhysicalSourceFubini.curryEquiv_represents_ae q,
    Measure.ae_ae_of_ae_prod hq] with k hk hrep
  exact Measure.ae_count_iff.mp (hk.trans hrep)

/-- Bosonic symmetry is retained by restricting the full coordinate isometry. -/
def sectorMomentum (m : ℕ) : Sector photonMeasure m →ₗᵢ[ℂ]
    Lp (Coefficient m) 2 (volume : Measure (Configuration m)) :=
  (fullMomentum m).comp (sectorInclusion photonMeasure m)

/-- Actual photon position coordinates use the L2 inverse Fourier transform. -/
def sectorPosition (m : ℕ) : Sector photonMeasure m →ₗᵢ[ℂ]
    Lp (Coefficient m) 2 (volume : Measure (Configuration m)) :=
  (Lp.fourierTransformₗᵢ (Configuration m) (Coefficient m)).symm.toLinearIsometry.comp
    (sectorMomentum m)

/-- Join the electronic coordinates to the actual photon position coordinates. -/
def spatialSectorPosition (N m : ℕ) :
    Lp (Sector photonMeasure m) 2 (volume : Measure (Configuration N)) →ₗᵢ[ℂ]
      Lp (Coefficient m) 2 (volume : Measure (Configuration (N + m))) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (configurationSplit N m)
    (configurationSplit_measurePreserving N m)).comp
    (PhysicalSourceFubini.curryEquiv.symm.toLinearIsometry.comp
      (liftIsometry volume (sectorPosition m)))

private def piIsometry {ι : Type*} [Fintype ι] {E F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (U : ∀ i, E i →ₗᵢ[ℂ] F i) : PiLp 2 E →ₗᵢ[ℂ] PiLp 2 F where
  toFun u := WithLp.toLp 2 (fun i => U i (u i))
  map_add' u v := by ext i; exact (U i).map_add _ _
  map_smul' c u := by ext i; exact (U i).map_smul _ _
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun r : ℝ => r ^ 2) ((U i).norm_map (u i)))

attribute [local irreducible] spatialSectorPosition PhysicalFiniteSectorCoordinates.coordinates

/-- The finite position-sector embedding is built on the actual number-supported space. -/
def finitePosition (N M : ℕ) :
    PhysicalFiniteSectorCoordinates.numberSubspace (Sector photonMeasure)
      (volume : Measure (Configuration N)) M →ₗᵢ[ℂ]
        PiLp 2 (fun m : Fin (M + 1) => Lp (Coefficient m.val) 2
          (volume : Measure (Configuration (N + m.val)))) :=
  (piIsometry (ι := Fin (M + 1))
    (E := fun m => Lp (Sector photonMeasure m.val) 2 (volume : Measure (Configuration N)))
    (F := fun m => Lp (Coefficient m.val) 2 (volume : Measure (Configuration (N + m.val))))
    (fun m => spatialSectorPosition N m.val)).comp
    (PhysicalFiniteSectorCoordinates.coordinates (Sector photonMeasure) volume M)

end GptLean.PhysicalSectorCoordinates
