import GptLean.PhotonLocalizationPhysicalCompactness
import GptLean.PhotonLocalizationFormBoundsSources

/-!
Local trace compactness for positive normal source operators.

Finite free-form expectation constructs the weak-form source vectors.
The number expectation supplies the number moment, and the normal trace
pairing supplies positivity, mass and square expansions. The conclusion
is total boundedness in the actual trace-class space.
-/

namespace GptLean.PhotonLocalization

open MeasureTheory Filter Topology
open PhotonLocalizationChannel
open scoped ENNReal

variable {N : ℕ} {K Hlocal T : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup Hlocal] [InnerProductSpace ℂ Hlocal] [CompleteSpace Hlocal]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {μ : Measure ElectronicPosition}

/-- Physical local compactness from free energy, localized mean number,
retained support and norm-convergent densities. The source expansion can
be the actual flattened Kraus expansion of the photon channel. -/
theorem normalSources_totallyBounded
    {R : K →ₗ.[ℂ] K}
    (S : SupportedFreeSpectrum (I := Fin N × Fin 3) R Hlocal)
    (sector : ℕ → K →L[ℂ] K)
    (hsector : ∀ k, IsStarProjection (sector k))
    (horthogonal : ∀ i j, i ≠ j → sector i * sector j = 0)
    (hR : ∀ k v w, (v, w) ∈ R.graph → (sector k v, sector k w) ∈ R.graph)
    (C : SpatialCutoffSupport S physicalElectronicFamily (numberSectorCutoff sector))
    (A : Gaussian.RankOneData (SpatialPhotonL2 (Fin N × Fin 3) K) T)
    (normal : NormalTraceData A) (F : NormalFunctionalData A)
    (Tr : RemovalState.PositiveTraceData T) (hpositive : A.positive ⊆ Tr.positive)
    (free : RemovalState.PositiveForm Tr) (number : T → ℝ≥0∞)
    (hgraph : ∀ v, free.expectation (A.rankOne v) < ⊤ →
      ∃ u : SpatialFreeVector (I := Fin N × Fin 3) R, u.value = v ∧
        free.expectation (A.rankOne v) = ENNReal.ofReal u.form)
    (x : ℕ → T) (hx : ∀ n, x n ∈ normal.states)
    (v : ℕ → ℕ → SpatialPhotonL2 (Fin N × Fin 3) K)
    (hsource : ∀ n, HasSum (fun k => A.rankOne (v n k)) (x n))
    (hsupport : ∀ n k, v n k ∈ S.photonSupport)
    {E B : ℝ} (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hfree : ∀ n, free.expectation (x n) ≤ ENNReal.ofReal E)
    (hnumber : ∀ n, number (x n) ≤ ENNReal.ofReal B)
    (hsectorTrace : ∀ n, HasSum
      (fun k => (F.repr (x n) ((sector k).compLpL 2 volume)).re) (F.repr (x n) 1).re)
    (hnumberSeries : ∀ n, number (x n) = ∑' k : ℕ, ENNReal.ofReal
      ((k : ℝ) * (F.repr (x n) ((sector k).compLpL 2 volume)).re))
    (ρ : ℕ → Lp ℝ 1 μ) (ν : ℕ → Measure (Fin N → ElectronicPosition))
    [∀ n, IsFiniteMeasure (ν n)]
    (hposition : ∀ n f, (F.repr (x n) (positionObservable f)).re = ∫ z, f z ∂ν n)
    (hdensity : ∀ n, ElectronicDensityMeasure (ν n) (ρ n))
    {ρlimit : Lp ℝ 1 μ} (hρ : Tendsto ρ atTop (𝓝 ρlimit)) :
    TotallyBounded (Set.range x) := by
  choose u hu hs hsum using fun n =>
    spatial_sources_of_finite_form free hpositive hgraph (hsource n) hE (hfree n)
  have hpos n := F.positive normal (hx n).1
  have hmass n : (F.repr (x n) 1).re ≤ 1 := by
    rw [F.mass normal (hx n).1, (hx n).2]
  have hmoment n := PhotonLocalizationFormBounds.number_moment_bounds number
    (fun k => (F.repr (x n) ((sector k).compLpL 2 volume)).re)
    (fun k => (hpos n).proj_re_nonneg (compLpL_projection _ (hsector k)))
    (hnumberSeries n) hB (hnumber n)
  have htb := spatialSources_totallyBounded_of_density_tendsto S sector hsector horthogonal
    hR C (fun n => F.repr (x n)) u
    (fun n a => by simpa only [hu] using F.square_trace (hsource n) a)
    hpos hmass (fun n k => by rw [hu]; exact hsupport n k)
    hs E hsum hsectorTrace (fun n => (hmoment n).1) B (fun n => (hmoment n).2)
    ρ ν hposition hdensity hρ
  apply (totallyBounded_image_iff F.isometry.isUniformInducing).mp
  simpa only [← Set.range_comp, Function.comp_def] using htb


/-- The compactness theorem applied to the constructed channel, using
its original spectral vectors and actual flattened Kraus expansion.
The density belongs to the original state and is carried through by
proved electronic observable preservation. -/
theorem channelSources_totallyBounded
    {R : K →ₗ.[ℂ] K}
    (S : SupportedFreeSpectrum (I := Fin N × Fin 3) R Hlocal)
    (sector : ℕ → K →L[ℂ] K)
    (hsector : ∀ k, IsStarProjection (sector k))
    (horthogonal : ∀ i j, i ≠ j → sector i * sector j = 0)
    (hR : ∀ k v w, (v, w) ∈ R.graph → (sector k v, sector k w) ∈ R.graph)
    (C : SpatialCutoffSupport S physicalElectronicFamily (numberSectorCutoff sector))
    (A : Gaussian.RankOneData (SpatialPhotonL2 (Fin N × Fin 3) K) T)
    (normal : NormalTraceData A) (F : NormalFunctionalData A)
    (Tr : RemovalState.PositiveTraceData T) (hpositive : A.positive ⊆ Tr.positive)
    (free : RemovalState.PositiveForm Tr) (number : T → ℝ≥0∞)
    (hgraph : ∀ v, free.expectation (A.rankOne v) < ⊤ →
      ∃ u : SpatialFreeVector (I := Fin N × Fin 3) R, u.value = v ∧
        free.expectation (A.rankOne v) = ENNReal.ofReal u.form)
    (U : KrausIsometry (SpatialPhotonL2 (Fin N × Fin 3) K))
    (x : ℕ → T) (hx : ∀ n, x n ∈ normal.states)
    (v : ℕ → ℕ → SpatialPhotonL2 (Fin N × Fin 3) K)
    (hsource : ∀ n, HasSum (fun k => A.rankOne (v n k)) (x n))
    (hsupport : ∀ w a, U w a ∈ S.photonSupport)
    {E B : ℝ} (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hfree : ∀ n, free.expectation (normal.extend U (x n)) ≤ ENNReal.ofReal E)
    (hnumber : ∀ n, number (normal.extend U (x n)) ≤ ENNReal.ofReal B)
    (hsectorTrace : ∀ n, HasSum
      (fun k => (F.repr (normal.extend U (x n)) ((sector k).compLpL 2 volume)).re) (F.repr (normal.extend U (x n)) 1).re)
    (hnumberSeries : ∀ n, number (normal.extend U (x n)) = ∑' k : ℕ, ENNReal.ofReal
      ((k : ℝ) * (F.repr (normal.extend U (x n)) ((sector k).compLpL 2 volume)).re))
    (ρ : ℕ → Lp ℝ 1 μ) (ν : ℕ → Measure (Fin N → ElectronicPosition))
    [∀ n, IsFiniteMeasure (ν n)]
    (hposition : ∀ n f, (F.repr (x n) (positionObservable f)).re = ∫ z, f z ∂ν n)
    (hintertwine : ∀ f w a, U (positionObservable f w) a = positionObservable f (U w a))
    (hdensity : ∀ n, ElectronicDensityMeasure (ν n) (ρ n))
    {ρlimit : Lp ℝ 1 μ} (hρ : Tendsto ρ atTop (𝓝 ρlimit)) :
    TotallyBounded (Set.range fun n => normal.extend U (x n)) := by
  apply normalSources_totallyBounded S sector hsector horthogonal hR C A normal F Tr
    hpositive free number hgraph (fun n => normal.extend U (x n))
    (fun n => normal.preserves_states U (hx n))
    (fun n => Repair.flattenVectors (fun i a => U (v n i) a))
    (fun n => normal.mixed_hasSum U (hsource n))
    (fun n k => hsupport _ _) hE hB hfree hnumber hsectorTrace hnumberSeries ρ ν
    (fun n f => ?_) hdensity hρ
  exact (congrArg Complex.re (F.electronic normal U (positionObservable f)
    (hintertwine f) (hx n).1)).trans (hposition n f)

end GptLean.PhotonLocalization
