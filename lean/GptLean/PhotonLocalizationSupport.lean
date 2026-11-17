import GptLean.PhotonLocalizationLocalFormsSpectral

/-!
Actual support subspaces for the local free form. Electronic support is
vanishing almost everywhere outside a spatial region. Photon and number
support are fibrewise membership in fixed closed subspaces of Fock space.
The five cutoff-support properties are derived from these predicates.
-/

noncomputable section

namespace GptLean.PhotonLocalization

open MeasureTheory Filter

section Subspaces

variable {Ω K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def fibreSupport (W : Submodule ℂ K) : Submodule ℂ (Lp K 2 μ) where
  carrier := {u | ∀ᵐ x ∂μ, u x ∈ W}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (α := Ω) (E := K) (p := 2) (μ := μ)] with x hx
    rw [hx]
    exact W.zero_mem
  add_mem' := by
    intro u v hu hv
    filter_upwards [hu, hv, Lp.coeFn_add u v] with x hx hy hz
    rw [hz]
    exact W.add_mem hx hy
  smul_mem' := by
    intro c u hu
    filter_upwards [hu, Lp.coeFn_smul c u] with x hx hy
    rw [hy]
    exact W.smul_mem c hx

def spatialSupport (s : Set Ω) : Submodule ℂ (Lp K 2 μ) where
  carrier := {u | ∀ᵐ x ∂μ, x ∉ s → u x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (α := Ω) (E := K) (p := 2) (μ := μ)] with x hx
    intro _
    exact hx
  add_mem' := by
    intro u v hu hv
    filter_upwards [hu, hv, Lp.coeFn_add u v] with x hx hy hz
    intro hs
    simp only [hz, Pi.add_apply, hx hs, hy hs, add_zero]
  smul_mem' := by
    intro c u hu
    filter_upwards [hu, Lp.coeFn_smul c u] with x hx hy
    intro hs
    simp only [hy, Pi.smul_apply, hx hs, smul_zero]

theorem compLpL_mem_fibreSupport
    (P : K →L[ℂ] K) (W : Submodule ℂ K) (hP : ∀ v ∈ W, P v ∈ W)
    (u : Lp K 2 μ) (hu : u ∈ fibreSupport W) :
    P.compLpL 2 μ u ∈ fibreSupport W := by
  filter_upwards [hu, P.coeFn_compLpL u] with x hx hp
  rw [hp]
  exact hP _ hx

theorem compLpL_mem_range (P : K →L[ℂ] K) (u : Lp K 2 μ) :
    P.compLpL 2 μ u ∈ fibreSupport (LinearMap.range P.toLinearMap) := by
  filter_upwards [P.coeFn_compLpL u] with x hx
  rw [hx]
  exact ⟨u x, rfl⟩

end Subspaces

variable {I K Hlocal : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Hlocal] [InnerProductSpace ℂ Hlocal]

theorem SmoothElectronicCutoff.mem_fibreSupport (Z : SmoothElectronicCutoff I)
    (W : Submodule ℂ K) (u : SpatialPhotonL2 I K) (hu : u ∈ fibreSupport W) :
    Z.operator u ∈ fibreSupport W := by
  filter_upwards [hu, Z.operator_apply u] with x hx hz
  rw [hz]
  simpa only [Complex.coe_smul] using W.smul_mem (Z.multiplier x : ℂ) hx

theorem SmoothElectronicCutoff.mem_spatialSupport (Z : SmoothElectronicCutoff I)
    (s : Set (EuclideanSpace ℝ I)) (hz : ∀ x ∉ s, Z.multiplier x = 0)
    (u : SpatialPhotonL2 I K) : Z.operator u ∈ spatialSupport s := by
  filter_upwards [Z.operator_apply u] with x hx
  intro hs
  rw [hx, hz x hs, zero_smul]

/-- Canonical support predicates discharge the support fields used to
construct the local vectors. Only the fibre number projection preserving
the retained-photon subspace is required from the Fock sector calculus. -/
theorem SpatialCutoffSupport.of_pointwise
    {R : K →ₗ.[ℂ] K} (S : SupportedFreeSpectrum (I := I) R Hlocal)
    (Z : ℕ → SmoothElectronicCutoff I) (P : ℕ → K →L[ℂ] K)
    (photon : Submodule ℂ K) (region : ℕ → Set (EuclideanSpace ℝ I))
    (hphoton : S.photonSupport = fibreSupport photon)
    (helectronic : ∀ L, S.electronicSupport L = spatialSupport (region L))
    (hnumber : ∀ M, S.numberSupport M = fibreSupport (LinearMap.range (P M).toLinearMap))
    (hP : ∀ M v, v ∈ photon → P M v ∈ photon)
    (hZ : ∀ L x, x ∉ region L → (Z L).multiplier x = 0) :
    SpatialCutoffSupport S Z P where
  photon_number M v hv := by
    rw [hphoton] at hv ⊢
    exact compLpL_mem_fibreSupport (P M) photon (hP M) v hv
  photon_electronic L v hv := by
    rw [hphoton] at hv ⊢
    exact (Z L).mem_fibreSupport photon v hv
  electronic_range L v := by
    rw [helectronic L]
    exact (Z L).mem_spatialSupport (region L) (hZ L) v
  number_range M v := by
    rw [hnumber M]
    exact compLpL_mem_range (P M) v
  number_electronic L M v hv := by
    rw [hnumber M] at hv ⊢
    exact (Z L).mem_fibreSupport _ v hv

end GptLean.PhotonLocalization
