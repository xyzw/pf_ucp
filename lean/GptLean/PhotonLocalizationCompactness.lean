import GptLean.PhotonLocalizationSpectralTrace

/-!
Local trace compactness from density tails and localized form vectors.

The local spectrum lives on the bounded configuration space and its
projection is extended by zero to the full Hilbert space. The actual
normal trace representation connects those vectors to the state.
Neither a compressed state, a spectral tail bound, a finite-dimensional
trace corner, nor precompactness is assumed.
-/

namespace GptLean.PhotonLocalization

open Filter Topology MeasureTheory
open PhotonTrace

variable {H Hlocal Ω : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Hlocal] [InnerProductSpace ℂ Hlocal] [CompleteSpace Hlocal]
  [MeasurableSpace Ω] {μ : Measure Ω}

/-- Localized form data before choosing the spectral cutoff. The local
embedding identifies the cut source vectors, and the form bound is
uniform in the number cutoff and in the state index. -/
structure LocalFormData
    (region : ℕ → Set Ω) (ρ : ℕ → Lp ℝ 1 μ)
    (φ : ℕ → (H →L[ℂ] H) →L[ℂ] ℂ) (Hlocal : Type*)
    [NormedAddCommGroup Hlocal] [InnerProductSpace ℂ Hlocal] [CompleteSpace Hlocal] where
  numberCutoff : ℕ → H →L[ℂ] H
  electronicCutoff : ℕ → H →L[ℂ] H
  number_projection : ∀ M, IsStarProjection (numberCutoff M)
  electronic_selfadjoint : ∀ L, IsSelfAdjoint (electronicCutoff L)
  commute : ∀ L M, Commute (electronicCutoff L) (numberCutoff M)
  spectrum : ℕ → ℕ → CompactSpectrum Hlocal
  embedding : ℕ → ℕ → Hlocal →ₗᵢ[ℂ] H
  source : ℕ → ℕ → H
  localVector : ℕ → ℕ → ℕ → ℕ → Hlocal
  trace : ∀ n (a : H →L[ℂ] H),
    (φ n (star a * a)).re = ∑' k, ‖a (source n k)‖ ^ 2
  local_identity : ∀ L M n k,
    (electronicCutoff L * numberCutoff M) (source n k) =
      embedding L M (localVector L M n k)
  local_finite : ∀ L M n k, (spectrum L M).FiniteEnergy (localVector L M n k)
  local_summable : ∀ L M n,
    Summable (fun k => (spectrum L M).form (localVector L M n k))
  energy : ℕ → ℝ
  local_energy : ∀ L M n,
    ∑' k, (spectrum L M).form (localVector L M n k) ≤ energy L
  numberBound : ℝ
  number_tail : ∀ M n, (φ n (1 - numberCutoff M)).re ≤ numberBound / (M + 1)
  electronic_tail : ∀ L n,
    (φ n ((1 - electronicCutoff L) ^ 2)).re ≤ densityTail region L (ρ n)

/-- The three-tail compactness witness is constructed from the localized
form and the actual L¹ density supremum. The spectral tail is proved from
the eigenvalue expansion, and the compression bound from positivity. -/
noncomputable def LocalFormData.compressionWitness
    {region : ℕ → Set Ω} {ρ : ℕ → Lp ℝ 1 μ}
    {φ : ℕ → (H →L[ℂ] H) →L[ℂ] ℂ}
    (F : LocalFormData region ρ φ Hlocal)
    (hφ : ∀ n, IsPosFunctional (φ n)) (hmass : ∀ n, (φ n 1).re ≤ 1)
    {mass : ℝ} (hρmass : ∀ n, ‖ρ n‖ ≤ mass) (htight : DensityTight region ρ) :
    CompressionWitness ((H →L[ℂ] H) →L[ℂ] ℂ) φ :=
  PhotonTrace.compressionWitness_of_density region ρ hρmass htight φ hφ hmass
    F.numberCutoff F.electronicCutoff
    (fun L M s => (F.spectrum L M).embeddedProjection (F.embedding L M) s)
    F.number_projection F.electronic_selfadjoint F.commute
    (fun L M s => (F.spectrum L M).embeddedProjection_isFiniteRankProj
      (F.embedding L M) s)
    F.numberBound F.energy F.number_tail F.electronic_tail
    (fun L M s n => (F.spectrum L M).trace_embedded_spectral_tail_le
      (F.embedding L M) s (φ n) (F.source n) (F.trace n)
      (F.electronicCutoff L * F.numberCutoff M) (F.localVector L M n)
      (F.local_identity L M n) (F.local_finite L M n)
      (F.local_summable L M n) (F.local_energy L M n))

/-- Local precompactness from the form construction and spatial tightness. -/
theorem LocalFormData.totallyBounded
    {region : ℕ → Set Ω} {ρ : ℕ → Lp ℝ 1 μ}
    {φ : ℕ → (H →L[ℂ] H) →L[ℂ] ℂ}
    (F : LocalFormData region ρ φ Hlocal)
    (hφ : ∀ n, IsPosFunctional (φ n)) (hmass : ∀ n, (φ n 1).re ≤ 1)
    {mass : ℝ} (hρmass : ∀ n, ‖ρ n‖ ≤ mass) (htight : DensityTight region ρ) :
    TotallyBounded (Set.range φ) :=
  (F.compressionWitness hφ hmass hρmass htight).totallyBounded

/-- Norm convergence of the physical densities supplies tightness and
their uniform mass bound, so no separate electronic error is required. -/
theorem LocalFormData.totallyBounded_of_density_tendsto
    {region : ℕ → Set Ω} {ρ : ℕ → Lp ℝ 1 μ}
    {φ : ℕ → (H →L[ℂ] H) →L[ℂ] ℂ}
    (F : LocalFormData region ρ φ Hlocal)
    (hφ : ∀ n, IsPosFunctional (φ n)) (hmass : ∀ n, (φ n 1).re ≤ 1)
    (hmeasurable : ∀ L, MeasurableSet (region L))
    (hmono : Monotone region) (hexhaust : ⋃ L, region L = Set.univ)
    {ρlimit : Lp ℝ 1 μ} (hρ : Tendsto ρ atTop (𝓝 ρlimit)) :
    TotallyBounded (Set.range φ) := by
  obtain ⟨mass, hmassρ⟩ := hρ.norm.bddAbove_range
  exact F.totallyBounded hφ hmass (fun n => hmassρ (Set.mem_range_self n))
    (densityTight_of_tendsto region hmeasurable hmono hexhaust hρ)

/-- Supply the existing closure interface with the proved compactness
construction. The normal trace representation is isometric, so total
boundedness in the functional norm is exactly trace-norm total
boundedness in the ambient state space. -/
noncomputable def CoarseData.ofLocalForms
    {X Test : Type*} [NormedAddCommGroup X]
    {D : PhotonLoss.LocalizationData X} {T : PhotonLoss.TraceData D Test}
    (repr : X → (H →L[ℂ] H) →L[ℂ] ℂ) (hrepr : Isometry repr)
    (hpositive : ∀ x ∈ D.states, IsPosFunctional (repr x))
    (hmass : ∀ x ∈ D.states, (repr x 1).re ≤ 1)
    (region : ℕ → Set Ω) (density : X → Lp ℝ 1 μ)
    (mass : ℝ) (hdensity : ∀ x ∈ D.states, ‖density x‖ ≤ mass)
    (localForms : ∀ (u : ℕ → X) (E : ℝ),
      (∀ n, u n ∈ D.states) →
      (∀ n, T.energy (u n) ≤ ENNReal.ofReal E) →
      DensityTight region (fun n => density (u n)) → ∀ m,
      Nonempty (LocalFormData region (fun n => density (u n))
        (fun n => repr (D.localize m (u n))) Hlocal))
    (rough : ℝ → ℝ)
    (hrough : ∀ E m, ∀ x ∈ D.states,
      T.energy x ≤ ENNReal.ofReal E →
      T.energy (D.localize m x) ≤ ENNReal.ofReal (rough E)) :
    CoarseData D T where
  electronicTight u := DensityTight region (fun n => density (u n))
  precompact u E hu hE htight m := by
    let F := (localForms u E hu hE htight m).some
    have htb := F.totallyBounded
      (fun n => hpositive _ (D.localize_state m _ (hu n)))
      (fun n => hmass _ (D.localize_state m _ (hu n)))
      (fun n => hdensity _ (hu n)) htight
    apply (totallyBounded_image_iff hrepr.isUniformInducing).mp
    simpa only [← Set.range_comp, Function.comp_def] using htb
  rough := rough
  rough_bound := hrough

end GptLean.PhotonLocalization
