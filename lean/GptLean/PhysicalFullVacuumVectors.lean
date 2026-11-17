import GptLean.PhysicalDarkFock
import GptLean.PhysicalFockVacuumSectors
import GptLean.PhysicalFockMomentumSupport
import GptLean.PhysicalPFVacuumInsertion

/-!
The full photon vacuum and its scalar electronic range.

Zero radiation energy kills every positive photon sector. The remaining
sector is the actual vacuum line. Its spatial lift identifies that range
with scalar electronic L² functions through an explicit inverse.
-/

noncomputable section

namespace GptLean.PhysicalFullVacuum

open MeasureTheory PhysicalFock PhysicalFock.DarkModes PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true

/-- The actual normalized photon vacuum. -/
def vacuum : PhotonFock := creationWord photonMeasure []

theorem vacuum_norm : ‖vacuum‖ = 1 := PhysicalFock.vacuum_norm photonMeasure

/-- Scalar multiplication by the actual vacuum. -/
def fiberInsertion : ℂ →ₗᵢ[ℂ] PhotonFock where
  toLinearMap := ((ContinuousLinearMap.id ℂ ℂ).smulRight vacuum).toLinearMap
  norm_map' z := by
    change ‖z • vacuum‖ = ‖z‖
    rw [norm_smul, vacuum_norm, mul_one]

@[simp] theorem fiberInsertion_apply (z : ℂ) : fiberInsertion z = z • vacuum := rfl

/-- The scalar coefficient of the photon vacuum. -/
def coefficient : PhotonFock →L[ℂ] ℂ := innerSL ℂ vacuum

@[simp] theorem coefficient_fiberInsertion (z : ℂ) : coefficient (fiberInsertion z) = z := by
  change ⟪vacuum, z • vacuum⟫_ℂ = z
  rw [inner_smul_right, inner_self_eq_one_of_norm_eq_one vacuum_norm, mul_one]

theorem darkVacuum_iff_positive_sectors_zero (u : PhotonFock) :
    DarkVacuum Set.univ u ↔ ∀ n : ℕ, u (n + 1) = 0 := by
  constructor
  · intro h n
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [h (n + 1), Lp.coeFn_zero ℂ 2 (SectorMeasure photonMeasure (n + 1))]
      with k hk hz
    change (u (n + 1)).val k = (0 : FullSector photonMeasure (n + 1)) k
    rw [hz]
    by_contra hne
    exact hk hne 0 (Set.mem_univ _)
  · intro h n
    cases n with
    | zero => exact ae_of_all _ fun _ _ i => Fin.elim0 i
    | succ n =>
      rw [h n]
      filter_upwards [Lp.coeFn_zero ℂ 2 (SectorMeasure photonMeasure (n + 1))] with k hk
      intro hne
      exact False.elim (hne hk)

theorem darkVacuum_iff_sector_fixed (u : PhotonFock) :
    DarkVacuum Set.univ u ↔ photonSector photonMeasure 0 u = u := by
  rw [darkVacuum_iff_positive_sectors_zero]
  constructor
  · intro h
    apply lp.ext
    funext n
    cases n with
    | zero => exact sector_coordinate (Sector photonMeasure) 0 u
    | succ n =>
      exact (sector_coordinate_ne (Sector photonMeasure) 0 (n + 1)
        (Nat.succ_ne_zero n) u).trans (h n).symm
  · intro h n
    have he := congrArg (fun v : PhotonFock => v (n + 1)) h
    exact he.symm.trans (sector_coordinate_ne (Sector photonMeasure) 0 (n + 1)
      (Nat.succ_ne_zero n) u)

theorem fiberInsertion_coefficient (BF : StandardSymmetricFockExponential)
    (u : PhotonFock) :
    fiberInsertion (coefficient u) = photonSector photonMeasure 0 u := by
  exact congrArg (fun L : PhotonFock →L[ℂ] PhotonFock => L u)
    (VacuumSectors.vacuumProjection_eq_sector photonMeasure (photonExponential BF))

theorem fiberInsertion_coefficient_of_darkVacuum (BF : StandardSymmetricFockExponential)
    (u : PhotonFock) (hu : DarkVacuum Set.univ u) :
    fiberInsertion (coefficient u) = u :=
  (fiberInsertion_coefficient BF u).trans ((darkVacuum_iff_sector_fixed u).mp hu)

theorem darkVacuum_fiberInsertion (BF : StandardSymmetricFockExponential) (z : ℂ) :
    DarkVacuum Set.univ (fiberInsertion z) := by
  apply (darkVacuum_iff_sector_fixed _).mpr
  rw [← fiberInsertion_coefficient BF, coefficient_fiberInsertion]

theorem darkVacuum_iff_scalar (BF : StandardSymmetricFockExponential) (u : PhotonFock) :
    DarkVacuum Set.univ u ↔ ∃ z : ℂ, fiberInsertion z = u := by
  constructor
  · intro hu
    exact ⟨coefficient u, fiberInsertion_coefficient_of_darkVacuum BF u hu⟩
  · rintro ⟨z, rfl⟩
    exact darkVacuum_fiberInsertion BF z

theorem darkVacuum_of_radiation_zero (u : PhotonFock) (hu : radiationForm u = 0) :
    DarkVacuum Set.univ u := by
  apply darkVacuum_of_moment MeasurableSet.univ u
  apply le_antisymm _ zero_le
  apply le_trans (b := photonMoment (fun p => ENNReal.ofReal ‖p.1‖) u)
  · apply ENNReal.tsum_le_tsum
    intro n
    apply lintegral_mono
    intro k
    apply mul_le_mul_left
    apply Finset.sum_le_sum
    intro i _
    apply ENNReal.ofReal_le_ofReal
    simp only [weight, Set.indicator_univ, NormalPhoton.frequency]
    exact min_le_left _ _
  · rw [photonMoment_frequency, hu]

theorem radiation_zero_of_darkVacuum (u : PhotonFock) (hu : DarkVacuum Set.univ u) :
    radiationForm u = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  cases n with
  | zero => simp [sectorRadiationForm, sectorDispersion]
  | succ n =>
    rw [(darkVacuum_iff_positive_sectors_zero u).mp hu n, sectorRadiationForm_zero]

theorem radiation_zero_iff_scalar (BF : StandardSymmetricFockExponential) (u : PhotonFock) :
    radiationForm u = 0 ↔ ∃ z : ℂ, fiberInsertion z = u :=
  ⟨fun h => (darkVacuum_iff_scalar BF u).mp (darkVacuum_of_radiation_zero u h),
    fun h => radiation_zero_of_darkVacuum u ((darkVacuum_iff_scalar BF u).mpr h)⟩

/-- Every full-dark Kraus output lies in the full photon vacuum. -/
theorem kraus_darkVacuum (BF : StandardSymmetricFockExponential) (u : PhotonFock) (a : ℕ) :
    DarkVacuum Set.univ (krausFock MeasurableSet.univ BF a u) := by
  have hgen := (physicalFockSubspaces BF).factor_mem (brightSplit MeasurableSet.univ)
    (MomentumSplit.supported photonMeasure Set.univᶜ MeasurableSet.univ.compl)
    (fun f => by
      rw [brightSplit, MomentumSplit.retained_split]
      exact MomentumSplit.projection_mem_supported photonMeasure Set.univᶜ
        MeasurableSet.univ.compl f) u a
  have hs := MomentumSupport.generated_le_fockSupport photonMeasure Set.univᶜ
    MeasurableSet.univ.compl hgen
  intro n
  have hn := (Submodule.mem_iInf _).mp hs n
  change ∀ᵐ k ∂SectorMeasure photonMeasure n,
    k ∉ MomentumSupport.productRegion n Set.univᶜ →
      (krausFock MeasurableSet.univ BF a u n).val k = 0 at hn
  filter_upwards [hn] with k hk hne i _
  apply hne
  apply hk
  intro hall
  exact hall i (Set.mem_univ _)

section Spatial

variable {X : Type} [MeasurableSpace X] (μ : Measure X)

/-- Vacuum insertion of scalar electronic wave functions. -/
def insertion : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp PhotonFock 2 μ :=
  PhysicalPFVacuumInsertion.spatialLift μ fiberInsertion

/-- Extraction of the scalar electronic vacuum coefficient. -/
def extraction : Lp PhotonFock 2 μ →L[ℂ] Lp ℂ 2 μ := coefficient.compLpL 2 μ

/-- Projection onto the full spatial vacuum range. -/
def projection : Lp PhotonFock 2 μ →L[ℂ] Lp PhotonFock 2 μ :=
  (insertion μ).toContinuousLinearMap.comp (extraction μ)

theorem insertion_ae (u : Lp ℂ 2 μ) :
    insertion μ u =ᵐ[μ] fun x => u x • vacuum :=
  PhysicalPFVacuumInsertion.spatialLift_ae μ fiberInsertion u

theorem extraction_ae (u : Lp PhotonFock 2 μ) :
    extraction μ u =ᵐ[μ] fun x => coefficient (u x) := coefficient.coeFn_compLpL u

@[simp] theorem extraction_insertion (u : Lp ℂ 2 μ) :
    extraction μ (insertion μ u) = u := by
  apply Lp.ext
  filter_upwards [extraction_ae μ (insertion μ u), insertion_ae μ u] with x he hi
  rw [he, hi]
  exact coefficient_fiberInsertion (u x)

theorem insertion_darkVacuum (BF : StandardSymmetricFockExponential) (u : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, DarkVacuum Set.univ (insertion μ u x) := by
  filter_upwards [insertion_ae μ u] with x hx
  rw [hx]
  exact darkVacuum_fiberInsertion BF (u x)

theorem insertion_extraction_of_ae_darkVacuum (BF : StandardSymmetricFockExponential)
    (u : Lp PhotonFock 2 μ) (hu : ∀ᵐ x ∂μ, DarkVacuum Set.univ (u x)) :
    insertion μ (extraction μ u) = u := by
  apply Lp.ext
  filter_upwards [insertion_ae μ (extraction μ u), extraction_ae μ u, hu] with x hi he hu
  rw [hi, he]
  exact fiberInsertion_coefficient_of_darkVacuum BF (u x) hu

theorem range_iff_ae_darkVacuum (BF : StandardSymmetricFockExponential)
    (u : Lp PhotonFock 2 μ) :
    (∃ v : Lp ℂ 2 μ, insertion μ v = u) ↔ ∀ᵐ x ∂μ, DarkVacuum Set.univ (u x) := by
  constructor
  · rintro ⟨v, rfl⟩
    exact insertion_darkVacuum μ BF v
  · intro hu
    exact ⟨extraction μ u, insertion_extraction_of_ae_darkVacuum μ BF u hu⟩

theorem projection_fixed_iff_range (u : Lp PhotonFock 2 μ) :
    projection μ u = u ↔ ∃ v : Lp ℂ 2 μ, insertion μ v = u := by
  constructor
  · intro hu
    exact ⟨extraction μ u, hu⟩
  · rintro ⟨v, rfl⟩
    change insertion μ (extraction μ (insertion μ v)) = insertion μ v
    rw [extraction_insertion]

/-- Full-dark Kraus coordinates lie in the scalar electronic vacuum range. -/
theorem projection_fullKraus (BF : StandardSymmetricFockExponential)
    (u : Lp PhotonFock 2 μ) (a : ℕ) :
    projection μ (KrausL2.lift μ ((photonFactorization BF).factor
      (brightSplit MeasurableSet.univ)) u a) =
        KrausL2.lift μ ((photonFactorization BF).factor
          (brightSplit MeasurableSet.univ)) u a := by
  apply insertion_extraction_of_ae_darkVacuum μ BF
  filter_upwards [KrausL2.lift_coordinate_ae μ ((photonFactorization BF).factor
    (brightSplit MeasurableSet.univ)) u a] with x hx
  rw [hx]
  exact kraus_darkVacuum BF (u x) a

end Spatial

end GptLean.PhysicalFullVacuum
