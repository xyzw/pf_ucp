import GptLean.PhotonLocalizationRellichSymbol
import GptLean.PhotonLocalizationLocalFormsSpectral
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
Rellich compactness for the actual finite-sector free form.

The imported analytic statement concerns supported H½ unit balls on any
bounded region. The free-form ball is put inside a finite product of
those compact sets using the proved Fourier-symbol inequality. A generic
compact-inclusion spectral theorem then constructs the local spectrum.
No compactness or spectrum of the physical free form is assumed.
-/

noncomputable section

namespace GptLean.PhotonLocalization

open MeasureTheory Set
open scoped ENNReal

abbrev PhotonSectorL2 (N m : ℕ) (E : Type*) [NormedAddCommGroup E] :=
  Lp E 2 (volume : Measure (PhotonSectorPosition N m))

def sectorFourierEnergy {N m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (F : PhotonSectorL2 N m E ≃ₗᵢ[ℂ] PhotonSectorL2 N m E)
    (symbol : PhotonSectorPosition N m → ℝ) (u : PhotonSectorL2 N m E) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (symbol ξ) * ‖F u ξ‖ₑ ^ 2

theorem sectorFourierEnergy_coercivity {N m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (F : PhotonSectorL2 N m E ≃ₗᵢ[ℂ] PhotonSectorL2 N m E)
    (u : PhotonSectorL2 N m E) :
    sectorFourierEnergy F (sectorHalfSymbol N m) u ≤
      sectorFourierEnergy F (sectorFreeSymbol N m) u := by
  apply lintegral_mono
  intro ξ
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (sector_symbol_coercivity N m ξ)) le_rfl

variable {N : ℕ} {E : ℕ → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, InnerProductSpace ℂ (E m)]
  [∀ m, CompleteSpace (E m)] [∀ m, FiniteDimensional ℂ (E m)]

/-- Universal Fourier and supported Rellich background. The coefficient
spaces are finite dimensional, covering spin and photon polarization.
The compactness statement applies to every bounded spatial set and the
standard joint H½ symbol, independently of cutoffs or source states. -/
structure SectorRellichBackground (N : ℕ) (E : ℕ → Type*)
    [∀ m, NormedAddCommGroup (E m)] [∀ m, InnerProductSpace ℂ (E m)]
    [∀ m, CompleteSpace (E m)] [∀ m, FiniteDimensional ℂ (E m)] where
  fourier : ∀ m, PhotonSectorL2 N m (E m) ≃ₗᵢ[ℂ] PhotonSectorL2 N m (E m)
  compact_half_ball : ∀ m (s : Set (PhotonSectorPosition N m)), Bornology.IsBounded s →
    IsCompact {u : PhotonSectorL2 N m (E m) |
      (∀ᵐ x ∂volume, x ∉ s → u x = 0) ∧
        sectorFourierEnergy (fourier m) (sectorHalfSymbol N m) u ≤ 1}

variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The usual finite-sector coordinate and Plancherel identification of
the supported form domain. `form_identity` is an equality of the actual
free kinetic/radiation form with its Fourier symbol, not a coercivity or
compactness estimate. -/
structure FiniteSectorRepresentation (B : SectorRellichBackground N E)
    (M : ℕ) (J : V →L[ℂ] H) (L r : ℝ) where
  sectors : H →ₗᵢ[ℂ] PiLp 2 (fun m : Fin (M + 1) => PhotonSectorL2 N m.val (E m.val))
  supported : ∀ w (m : Fin (M + 1)), ∀ᵐ x ∂volume,
    x ∉ sectorConfigurationRegion N m.val L r → sectors w m x = 0
  form_identity : ∀ v,
    (∑ m : Fin (M + 1), sectorFourierEnergy (B.fourier m.val)
      (sectorFreeSymbol N m.val) (sectors (J v) m)) = ENNReal.ofReal (‖v‖ ^ 2)

namespace FiniteSectorRepresentation

variable {B : SectorRellichBackground N E} {M : ℕ} {J : V →L[ℂ] H} {L r : ℝ}

/-- Free-form control of every sector's joint H½ norm. -/
theorem half_energy_le (D : FiniteSectorRepresentation B M J L r)
    (v : V) (m : Fin (M + 1)) :
    sectorFourierEnergy (B.fourier m.val) (sectorHalfSymbol N m.val)
      (D.sectors (J v) m) ≤ ENNReal.ofReal (‖v‖ ^ 2) := by
  calc
    _ ≤ sectorFourierEnergy (B.fourier m.val) (sectorFreeSymbol N m.val)
        (D.sectors (J v) m) := sectorFourierEnergy_coercivity _ _
    _ ≤ ∑ j : Fin (M + 1), sectorFourierEnergy (B.fourier j.val)
        (sectorFreeSymbol N j.val) (D.sectors (J v) j) :=
      Finset.single_le_sum (f := fun j : Fin (M + 1) =>
        sectorFourierEnergy (B.fourier j.val) (sectorFreeSymbol N j.val)
          (D.sectors (J v) j)) (fun _ _ => bot_le) (Finset.mem_univ m)
    _ = _ := D.form_identity v

/-- The compactness needed by the spectral theorem is proved from the
actual bounded sector supports, the joint symbol and finite products. -/
theorem totallyBounded_form_ball (D : FiniteSectorRepresentation B M J L r)
    (hL : 0 ≤ L) (hr : 0 ≤ r) :
    TotallyBounded (J '' Metric.closedBall (0 : V) 1) := by
  let C (m : Fin (M + 1)) : Set (PhotonSectorL2 N m.val (E m.val)) :=
    {u | (∀ᵐ x ∂volume, x ∉ sectorConfigurationRegion N m.val L r → u x = 0) ∧
      sectorFourierEnergy (B.fourier m.val) (sectorHalfSymbol N m.val) u ≤ 1}
  have hC (m : Fin (M + 1)) : IsCompact (C m) :=
    B.compact_half_ball m.val _ (sectorConfigurationRegion_bounded N m.val hL hr)
  have hp := isCompact_univ_pi hC
  have hc : IsCompact ((WithLp.toLp 2) '' Set.pi Set.univ C) :=
    hp.image (PiLp.continuous_toLp 2 _)
  have hi : D.sectors '' (J '' Metric.closedBall (0 : V) 1) ⊆
      (WithLp.toLp 2) '' Set.pi Set.univ C := by
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨fun m => D.sectors (J v) m, ?_, rfl⟩
    intro m _
    refine ⟨D.supported (J v) m, (D.half_energy_le v m).trans ?_⟩
    have hn : ‖v‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    have hs : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
    simpa using ENNReal.ofReal_le_ofReal hs
  exact (totallyBounded_image_iff D.sectors.isometry.isUniformInducing).mp
    (hc.totallyBounded.subset hi)

end FiniteSectorRepresentation

/-- Generic spectral theorem for a densely defined closed positive form
with compact inclusion. A countably infinite Hilbert basis states the
scope needed by the existing `CompactSpectrum` representation. -/
structure CompactFormSpectralBackground (H V : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] where
  resolve : HilbertBasis ℕ ℂ H → ∀ J : V →L[ℂ] H,
    Function.Injective J → DenseRange J → (∀ v, ‖J v‖ ≤ ‖v‖) →
    TotallyBounded (J '' Metric.closedBall (0 : V) 1) →
    ∃ K : CompactSpectrum H, ∀ v,
      K.FiniteEnergy (J v) ∧ K.form (J v) = ‖v‖ ^ 2

variable [CompleteSpace H] [CompleteSpace V]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {R : K →ₗ.[ℂ] K}

/-- The Hilbert graph realization of the zero-extended supported free
form. All identities are about the domain and its graph norm. No local
estimate or spectrum occurs in this representation. -/
structure LocalFreeGraph (embedding : H →ₗᵢ[ℂ] SpatialPhotonL2 (Fin N × Fin 3) K)
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] where
  inclusion : V →L[ℂ] H
  injective : Function.Injective inclusion
  dense : DenseRange inclusion
  vector : V → SpatialFreeVector (I := Fin N × Fin 3) R
  extension : ∀ v, embedding (inclusion v) = (vector v).value
  graph_norm : ∀ v, (vector v).form = ‖v‖ ^ 2
  covers : ∀ w (u : SpatialFreeVector (I := Fin N × Fin 3) R),
    embedding w = u.value → ∃ v, inclusion v = w ∧ ‖v‖ ^ 2 = u.form

namespace LocalFreeGraph

variable {embedding : H →ₗᵢ[ℂ] SpatialPhotonL2 (Fin N × Fin 3) K}

omit [CompleteSpace H] in
theorem inclusion_norm_le (G : LocalFreeGraph (R := R) embedding V) (v : V) :
    ‖G.inclusion v‖ ≤ ‖v‖ := by
  have h := (G.vector v).mass_le_form
  rw [G.graph_norm, ← G.extension, embedding.norm_map] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- This is the actual application of the generic spectral theorem.
Its compactness premise is discharged by the preceding Rellich proof. -/
theorem exists_spectrum (G : LocalFreeGraph (R := R) embedding V)
    (B : SectorRellichBackground N E) (M : ℕ) {L r : ℝ}
    (D : FiniteSectorRepresentation B M G.inclusion L r)
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (spectral : CompactFormSpectralBackground H V) (basis : HilbertBasis ℕ ℂ H) :
    ∃ S : CompactSpectrum H, ∀ w (u : SpatialFreeVector (I := Fin N × Fin 3) R),
      embedding w = u.value → S.FiniteEnergy w ∧ S.form w = u.form := by
  obtain ⟨S, hS⟩ := spectral.resolve basis G.inclusion G.injective G.dense
    G.inclusion_norm_le (D.totallyBounded_form_ball hL hr)
  refine ⟨S, fun w u hu => ?_⟩
  obtain ⟨v, hv, he⟩ := G.covers w u hu
  simpa only [hv, he] using hS v

end LocalFreeGraph

end GptLean.PhotonLocalization
