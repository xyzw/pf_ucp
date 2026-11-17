import GptLean.PhotonLocalizationLocalFormsCutoff
import GptLean.PhotonLocalizationLocalFormsOperators
import GptLean.PhotonLocalizationSupport
import GptLean.PhotonLocalizationPosition

/-!
Local trace compactness assembled from physical spatial source vectors.

The electronic product cutoff, its derivative cost, number-sector tail,
density tail, local form vectors, spectral tail and finite-dimensional
compression are constructed by the preceding modules. The inputs below
are source trace/form expansions and the universal position, sector and
restricted-form identifications. There is no localized form estimate,
cutoff-tail estimate, compression witness or precompactness premise.
-/

noncomputable section

namespace GptLean.PhotonLocalization

open MeasureTheory

variable {N : ℕ} {K Hlocal : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup Hlocal] [InnerProductSpace ℂ Hlocal] [CompleteSpace Hlocal]
  {μ : Measure ElectronicPosition}

/-- Radii start at one, as required by the electronic product estimate. -/
def physicalElectronicRegion (L : ℕ) : Set ElectronicPosition :=
  Metric.closedBall 0 ((L : ℝ) + 1)

def physicalElectronicFamily (L : ℕ) : SmoothElectronicCutoff (Fin N × Fin 3) :=
  physicalElectronicCutoff ((L : ℝ) + 1) (by positivity)

/-- Construct every field of `LocalFormData` from actual spatial source
vectors. In particular, all three tails and the local ensemble estimate
are consequences, not assumptions of this constructor. -/
def LocalFormData.ofSpatialSources
    {R : K →ₗ.[ℂ] K}
    (S : SupportedFreeSpectrum (I := Fin N × Fin 3) R Hlocal)
    (sector : ℕ → K →L[ℂ] K)
    (hsector : ∀ k, IsStarProjection (sector k))
    (horthogonal : ∀ i j, i ≠ j → sector i * sector j = 0)
    (hR : ∀ k v w, (v, w) ∈ R.graph → (sector k v, sector k w) ∈ R.graph)
    (C : SpatialCutoffSupport S physicalElectronicFamily (numberSectorCutoff sector))
    (φ : ℕ → (SpatialPhotonL2 (Fin N × Fin 3) K →L[ℂ]
      SpatialPhotonL2 (Fin N × Fin 3) K) →L[ℂ] ℂ)
    (u : ℕ → ℕ → SpatialFreeVector (I := Fin N × Fin 3) R)
    (htrace : ∀ n a, (φ n (star a * a)).re = ∑' k, ‖a (u n k).value‖ ^ 2)
    (hpositive : ∀ n, PhotonTrace.IsPosFunctional (φ n))
    (hmass : ∀ n, (φ n 1).re ≤ 1)
    (hsupport : ∀ n k, (u n k).value ∈ S.photonSupport)
    (hsummable : ∀ n, Summable (fun k => (u n k).form))
    (E : ℝ) (hE : ∀ n, ∑' k, (u n k).form ≤ E)
    (hsectorTrace : ∀ n, HasSum (fun k => (φ n ((sector k).compLpL 2 volume)).re)
      (φ n 1).re)
    (hmean : ∀ n, Summable (fun k : ℕ =>
      (k : ℝ) * (φ n ((sector k).compLpL 2 volume)).re))
    (B : ℝ) (hB : ∀ n, ∑' k : ℕ,
      (k : ℝ) * (φ n ((sector k).compLpL 2 volume)).re ≤ B)
    (ρ : ℕ → Lp ℝ 1 μ) (ν : ℕ → Measure (Fin N → ElectronicPosition))
    [∀ n, IsFiniteMeasure (ν n)]
    (hposition : ∀ n f, (φ n (positionObservable f)).re = ∫ x, f x ∂ν n)
    (hdensity : ∀ n, ElectronicDensityMeasure (ν n) (ρ n)) :
    LocalFormData physicalElectronicRegion ρ φ Hlocal where
  numberCutoff M := (numberSectorCutoff sector M).compLpL 2 volume
  electronicCutoff L := (physicalElectronicFamily L).operator
  number_projection M := compLpL_projection _
    (numberSectorCutoff_projection sector hsector horthogonal M)
  electronic_selfadjoint L := (physicalElectronicFamily L).operator_selfadjoint
  commute L M := (physicalElectronicFamily L).operator_commute _
  spectrum := S.spectrum
  embedding := S.embedding
  source n k := (u n k).value
  localVector L M n k := C.localVector L M (u n k).value (hsupport n k)
  trace := htrace
  local_identity L M n k := (C.localVector_identity L M _ (hsupport n k)).symm
  local_finite L M n k := C.localVector_finite L M (numberSectorCutoff_graph sector hR M) (u n k) (hsupport n k)
  local_summable L M n := C.localVector_form_summable L M
    (projection_norm_le _ (numberSectorCutoff_projection sector hsector horthogonal M)) (numberSectorCutoff_graph sector hR M) (u n) (hsupport n) (hsummable n)
  energy L := 2 * E + 2 * Fintype.card (Fin N × Fin 3) *
    (physicalElectronicFamily (N := N) L).derivativeBound ^ 2
  local_energy L M n := by
    have hm : ∑' k, ‖(u n k).value‖ ^ 2 ≤ 1 := by
      have ht := htrace n 1
      simp only [star_one, one_mul, one_apply_eq_self] at ht
      exact ht.symm.trans_le (hmass n)
    simpa only [mul_one] using C.localVector_form_tsum_le L M
      (projection_norm_le _ (numberSectorCutoff_projection sector hsector horthogonal M)) (numberSectorCutoff_graph sector hR M) (u n) (hsupport n) (hsummable n) (hE n) hm
  numberBound := B
  number_tail M n := by
    rw [numberSectorCutoff_compLpL]
    exact numberSectorCutoff_tail_le _
      (fun k => compLpL_projection _ (hsector k)) (φ n) (hpositive n)
      (hsectorTrace n) (hmean n) (hB n) M
  electronic_tail L n := by
    let position := physicalPositionTrace (φ n) (ν n) (hposition n)
    have hc : position.cutoff ((L : ℝ) + 1) =
        (physicalElectronicFamily (N := N) L).operator :=
      positionObservable_cutoff _ (by positivity)
    rw [← hc]
    exact position.tail_le (ρ n) (hdensity n) (by positivity)


/-- Norm convergence of the actual densities gives local trace-norm
precompactness for these same physical source operators. -/
theorem spatialSources_totallyBounded_of_density_tendsto
    {R : K →ₗ.[ℂ] K}
    (S : SupportedFreeSpectrum (I := Fin N × Fin 3) R Hlocal)
    (sector : ℕ → K →L[ℂ] K)
    (hsector : ∀ k, IsStarProjection (sector k))
    (horthogonal : ∀ i j, i ≠ j → sector i * sector j = 0)
    (hR : ∀ k v w, (v, w) ∈ R.graph → (sector k v, sector k w) ∈ R.graph)
    (C : SpatialCutoffSupport S physicalElectronicFamily (numberSectorCutoff sector))
    (φ : ℕ → (SpatialPhotonL2 (Fin N × Fin 3) K →L[ℂ]
      SpatialPhotonL2 (Fin N × Fin 3) K) →L[ℂ] ℂ)
    (u : ℕ → ℕ → SpatialFreeVector (I := Fin N × Fin 3) R)
    (htrace : ∀ n a, (φ n (star a * a)).re = ∑' k, ‖a (u n k).value‖ ^ 2)
    (hpositive : ∀ n, PhotonTrace.IsPosFunctional (φ n))
    (hmass : ∀ n, (φ n 1).re ≤ 1)
    (hsupport : ∀ n k, (u n k).value ∈ S.photonSupport)
    (hsummable : ∀ n, Summable (fun k => (u n k).form))
    (E : ℝ) (hE : ∀ n, ∑' k, (u n k).form ≤ E)
    (hsectorTrace : ∀ n, HasSum (fun k => (φ n ((sector k).compLpL 2 volume)).re)
      (φ n 1).re)
    (hmean : ∀ n, Summable (fun k : ℕ =>
      (k : ℝ) * (φ n ((sector k).compLpL 2 volume)).re))
    (B : ℝ) (hB : ∀ n, ∑' k : ℕ,
      (k : ℝ) * (φ n ((sector k).compLpL 2 volume)).re ≤ B)
    (ρ : ℕ → Lp ℝ 1 μ) (ν : ℕ → Measure (Fin N → ElectronicPosition))
    [∀ n, IsFiniteMeasure (ν n)]
    (hposition : ∀ n f, (φ n (positionObservable f)).re = ∫ x, f x ∂ν n)
    (hdensity : ∀ n, ElectronicDensityMeasure (ν n) (ρ n))
    {ρlimit : Lp ℝ 1 μ} (hρ : Filter.Tendsto ρ Filter.atTop (nhds ρlimit)) :
    TotallyBounded (Set.range φ) := by
  let F := LocalFormData.ofSpatialSources S sector hsector horthogonal hR C φ u htrace
    hpositive hmass hsupport hsummable E hE hsectorTrace hmean B hB ρ ν hposition hdensity
  apply F.totallyBounded_of_density_tendsto hpositive hmass
    (fun _ => measurableSet_closedBall) ?_ ?_ hρ
  · intro L M hLM
    apply Metric.closedBall_subset_closedBall
    exact_mod_cast Nat.add_le_add_right hLM 1
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨L, hL⟩ := exists_nat_ge ‖x‖
    apply Set.mem_iUnion.mpr
    refine ⟨L, ?_⟩
    change dist x 0 ≤ (L : ℝ) + 1
    rw [dist_zero_right]
    linarith

end GptLean.PhotonLocalization
