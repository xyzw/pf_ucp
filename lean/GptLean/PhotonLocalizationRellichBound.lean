import GptLean.PhotonLocalizationRellichSpectrum

/-!
The finite-sector Rellich argument requires an upper bound by the exact
free graph norm, rather than equality with a chosen Fourier normalization.
The resulting compact spectrum still has the exact physical free form.
-/

noncomputable section

namespace GptLean.PhotonLocalization

open MeasureTheory Set
open scoped ENNReal

variable {N : ℕ} {E : ℕ → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, InnerProductSpace ℂ (E m)]
  [∀ m, CompleteSpace (E m)] [∀ m, FiniteDimensional ℂ (E m)]
  {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeH : CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [completeV : CompleteSpace V]

omit [CompleteSpace H] [CompleteSpace V] in
/-- Supported sector coordinates with controlled H½ energy give compact inclusion. -/
theorem totallyBounded_form_ball_of_sector_bound
    (B : SectorRellichBackground N E) (M : ℕ) (J : V →L[ℂ] H) {L r : ℝ}
    (sectors : H →ₗᵢ[ℂ] PiLp 2
      (fun m : Fin (M + 1) => PhotonSectorL2 N m.val (E m.val)))
    (supported : ∀ w (m : Fin (M + 1)), ∀ᵐ x ∂volume,
      x ∉ sectorConfigurationRegion N m.val L r → sectors w m x = 0)
    (bound : ∀ v (m : Fin (M + 1)),
      sectorFourierEnergy (B.fourier m.val) (sectorHalfSymbol N m.val)
        (sectors (J v) m) ≤ ENNReal.ofReal (‖v‖ ^ 2))
    (hL : 0 ≤ L) (hr : 0 ≤ r) :
    TotallyBounded (J '' Metric.closedBall (0 : V) 1) := by
  let C (m : Fin (M + 1)) : Set (PhotonSectorL2 N m.val (E m.val)) :=
    {u | (∀ᵐ x ∂volume, x ∉ sectorConfigurationRegion N m.val L r → u x = 0) ∧
      sectorFourierEnergy (B.fourier m.val) (sectorHalfSymbol N m.val) u ≤ 1}
  have hC (m : Fin (M + 1)) : IsCompact (C m) :=
    B.compact_half_ball m.val _ (sectorConfigurationRegion_bounded N m.val hL hr)
  have hc : IsCompact ((WithLp.toLp 2) '' Set.pi Set.univ C) :=
    (isCompact_univ_pi hC).image (PiLp.continuous_toLp 2 _)
  have hi : sectors '' (J '' Metric.closedBall (0 : V) 1) ⊆
      (WithLp.toLp 2) '' Set.pi Set.univ C := by
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨fun m => sectors (J v) m, ?_, rfl⟩
    intro m _
    refine ⟨supported (J v) m, (bound v m).trans ?_⟩
    have hn : ‖v‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    have hs : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
    simpa using ENNReal.ofReal_le_ofReal hs
  exact (totallyBounded_image_iff sectors.isometry.isUniformInducing).mp
    (hc.totallyBounded.subset hi)

omit completeH completeV in
/-- The prior exact sector representation supplies the weaker hypothesis directly. -/
theorem FiniteSectorRepresentation.totallyBounded_via_bound
    {B : SectorRellichBackground N E} {M : ℕ} {J : V →L[ℂ] H} {L r : ℝ}
    (D : FiniteSectorRepresentation B M J L r) (hL : 0 ≤ L) (hr : 0 ≤ r) :
    TotallyBounded (J '' Metric.closedBall (0 : V) 1) :=
  totallyBounded_form_ball_of_sector_bound B M J D.sectors D.supported D.half_energy_le hL hr

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [completeK : CompleteSpace K]
  {R : K →ₗ.[ℂ] K}

omit completeK in
/-- Fourier coercive control constructs a spectrum with the exact graph energy. -/
theorem LocalFreeGraph.exists_spectrum_of_sector_bound
    {embedding : H →ₗᵢ[ℂ] SpatialPhotonL2 (Fin N × Fin 3) K}
    (G : LocalFreeGraph (R := R) embedding V)
    (B : SectorRellichBackground N E) (M : ℕ) {L r : ℝ}
    (sectors : H →ₗᵢ[ℂ] PiLp 2
      (fun m : Fin (M + 1) => PhotonSectorL2 N m.val (E m.val)))
    (supported : ∀ w (m : Fin (M + 1)), ∀ᵐ x ∂volume,
      x ∉ sectorConfigurationRegion N m.val L r → sectors w m x = 0)
    (bound : ∀ v (m : Fin (M + 1)),
      sectorFourierEnergy (B.fourier m.val) (sectorHalfSymbol N m.val)
        (sectors (G.inclusion v) m) ≤ ENNReal.ofReal (‖v‖ ^ 2))
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (spectral : CompactFormSpectralBackground H V) (basis : HilbertBasis ℕ ℂ H) :
    ∃ S : CompactSpectrum H, ∀ w (u : SpatialFreeVector (I := Fin N × Fin 3) R),
      embedding w = u.value → S.FiniteEnergy w ∧ S.form w = u.form := by
  obtain ⟨S, hS⟩ := spectral.resolve basis G.inclusion G.injective G.dense
    G.inclusion_norm_le
    (totallyBounded_form_ball_of_sector_bound B M G.inclusion sectors supported bound hL hr)
  refine ⟨S, fun w u hu => ?_⟩
  obtain ⟨v, hv, he⟩ := G.covers w u hu
  simpa only [hv, he] using hS v

variable {Vlocal : ℕ → ℕ → Type*}
  [∀ L M, NormedAddCommGroup (Vlocal L M)] [∀ L M, InnerProductSpace ℂ (Vlocal L M)]
  [∀ L M, CompleteSpace (Vlocal L M)]

/-- The same supported spectrum interface accepts Fourier bounds without changing its form. -/
def SupportedFreeSpectrum.ofRellichBound
    (photon : Submodule ℂ (SpatialPhotonL2 (Fin N × Fin 3) K))
    (electronic number : ℕ → Submodule ℂ (SpatialPhotonL2 (Fin N × Fin 3) K))
    (embedding : ℕ → ℕ → H →ₗᵢ[ℂ] SpatialPhotonL2 (Fin N × Fin 3) K)
    (hrange : ∀ L M, Set.range (embedding L M) =
      ↑(photon ⊓ electronic L ⊓ number M))
    (graph : ∀ L M, LocalFreeGraph (R := R) (embedding L M) (Vlocal L M))
    (rellich : SectorRellichBackground N E) {r : ℝ} (hr : 0 < r)
    (sectors : ∀ (_L M : ℕ), H →ₗᵢ[ℂ] PiLp 2
      (fun m : Fin (M + 1) => PhotonSectorL2 N m.val (E m.val)))
    (supported : ∀ (L M : ℕ) w (m : Fin (M + 1)), ∀ᵐ x ∂volume,
      x ∉ sectorConfigurationRegion N m.val ((L : ℝ) + 1) r → sectors L M w m x = 0)
    (bound : ∀ L M v (m : Fin (M + 1)),
      sectorFourierEnergy (rellich.fourier m.val) (sectorHalfSymbol N m.val)
        (sectors L M ((graph L M).inclusion v) m) ≤ ENNReal.ofReal (‖v‖ ^ 2))
    (spectral : ∀ L M, CompactFormSpectralBackground H (Vlocal L M))
    (basis : HilbertBasis ℕ ℂ H) :
    SupportedFreeSpectrum (I := Fin N × Fin 3) R H where
  photonSupport := photon
  electronicSupport := electronic
  numberSupport := number
  spectrum L M := ((graph L M).exists_spectrum_of_sector_bound rellich M
    (sectors L M) (supported L M) (bound L M) (by positivity) hr.le (spectral L M) basis).choose
  embedding := embedding
  range_eq := hrange
  free_form L M := ((graph L M).exists_spectrum_of_sector_bound rellich M
    (sectors L M) (supported L M) (bound L M) (by positivity) hr.le (spectral L M) basis).choose_spec

end GptLean.PhotonLocalization
