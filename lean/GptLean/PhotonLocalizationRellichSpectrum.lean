import GptLean.PhotonLocalizationRellich

/-! The local spectrum family is constructed by applying the proved
finite-sector Rellich argument and the generic compact-form spectral
theorem to the supported free graph at each pair of cutoffs. -/

noncomputable section

namespace GptLean.PhotonLocalization

open MeasureTheory

variable {N : ℕ} {K H : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R : K →ₗ.[ℂ] K}
  {E : ℕ → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, InnerProductSpace ℂ (E m)]
  [∀ m, CompleteSpace (E m)] [∀ m, FiniteDimensional ℂ (E m)]
  {V : ℕ → ℕ → Type*}
  [∀ L M, NormedAddCommGroup (V L M)] [∀ L M, InnerProductSpace ℂ (V L M)]
  [∀ L M, CompleteSpace (V L M)]

/-- Rellich and the compact-inclusion spectral theorem construct the
local compact spectrum. The inputs describe actual graph domains, finite
sector coordinates and their Plancherel identity. -/
def SupportedFreeSpectrum.ofRellich
    (photon : Submodule ℂ (SpatialPhotonL2 (Fin N × Fin 3) K))
    (electronic number : ℕ → Submodule ℂ (SpatialPhotonL2 (Fin N × Fin 3) K))
    (embedding : ℕ → ℕ → H →ₗᵢ[ℂ] SpatialPhotonL2 (Fin N × Fin 3) K)
    (hrange : ∀ L M, Set.range (embedding L M) =
      ↑(photon ⊓ electronic L ⊓ number M))
    (graph : ∀ L M, LocalFreeGraph (R := R) (embedding L M) (V L M))
    (rellich : SectorRellichBackground N E) {r : ℝ} (hr : 0 < r)
    (sectors : ∀ L M, FiniteSectorRepresentation rellich M (graph L M).inclusion
      ((L : ℝ) + 1) r)
    (spectral : ∀ L M, CompactFormSpectralBackground H (V L M))
    (basis : HilbertBasis ℕ ℂ H) :
    SupportedFreeSpectrum (I := Fin N × Fin 3) R H where
  photonSupport := photon
  electronicSupport := electronic
  numberSupport := number
  spectrum L M := ((graph L M).exists_spectrum rellich M (sectors L M)
    (by positivity) hr.le (spectral L M) basis).choose
  embedding := embedding
  range_eq := hrange
  free_form L M := ((graph L M).exists_spectrum rellich M (sectors L M)
    (by positivity) hr.le (spectral L M) basis).choose_spec

end GptLean.PhotonLocalization
