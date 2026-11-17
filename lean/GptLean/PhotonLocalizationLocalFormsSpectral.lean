import GptLean.PhotonLocalizationLocalForms

/-!
From the actual weak free form to the local spectrum.

The spectral background identifies the restricted form on every vector
of the supported subspace, with all derivatives computed after extension
by zero. The cut vectors, their form-domain membership, their summability
and the uniform ensemble estimate are conclusions.
-/

noncomputable section

namespace GptLean.PhotonLocalization

open MeasureTheory Filter
open scoped ENNReal

variable {I K Hlocal : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Hlocal] [InnerProductSpace ℂ Hlocal]

/-- The ordinary restricted free-form spectral theorem. The support
subspaces represent retained photons, bounded electronic positions and
finitely many photon sectors. This statement is uniform for every free
form vector in their intersection. -/
structure SupportedFreeSpectrum (R : K →ₗ.[ℂ] K) (Hlocal : Type*)
    [NormedAddCommGroup Hlocal] [InnerProductSpace ℂ Hlocal] where
  photonSupport : Submodule ℂ (SpatialPhotonL2 I K)
  electronicSupport : ℕ → Submodule ℂ (SpatialPhotonL2 I K)
  numberSupport : ℕ → Submodule ℂ (SpatialPhotonL2 I K)
  spectrum : ℕ → ℕ → CompactSpectrum Hlocal
  embedding : ℕ → ℕ → Hlocal →ₗᵢ[ℂ] SpatialPhotonL2 I K
  range_eq : ∀ L M,
    Set.range (embedding L M) =
      ↑(photonSupport ⊓ electronicSupport L ⊓ numberSupport M)
  free_form : ∀ L M (w : Hlocal) (u : SpatialFreeVector (I := I) R),
    embedding L M w = u.value →
      (spectrum L M).FiniteEnergy w ∧ (spectrum L M).form w = u.form

/-- Elementary support properties of the multiplier and the fibre number
projection, before choosing source states or a spectral cutoff. -/
structure SpatialCutoffSupport {R : K →ₗ.[ℂ] K}
    (S : SupportedFreeSpectrum (I := I) R Hlocal)
    (Z : ℕ → SmoothElectronicCutoff I) (P : ℕ → K →L[ℂ] K) where
  photon_number : ∀ M v, v ∈ S.photonSupport →
    (P M).compLpL 2 volume v ∈ S.photonSupport
  photon_electronic : ∀ L v, v ∈ S.photonSupport →
    (Z L).operator v ∈ S.photonSupport
  electronic_range : ∀ L v, (Z L).operator v ∈ S.electronicSupport L
  number_range : ∀ M v, (P M).compLpL 2 volume v ∈ S.numberSupport M
  number_electronic : ∀ L M v, v ∈ S.numberSupport M →
    (Z L).operator v ∈ S.numberSupport M

namespace SpatialCutoffSupport

variable {R : K →ₗ.[ℂ] K} {S : SupportedFreeSpectrum (I := I) R Hlocal}
  {Z : ℕ → SmoothElectronicCutoff I} {P : ℕ → K →L[ℂ] K}

theorem cut_mem (C : SpatialCutoffSupport S Z P) (L M : ℕ)
    (v : SpatialPhotonL2 I K) (hv : v ∈ S.photonSupport) :
    (Z L).operator ((P M).compLpL 2 volume v) ∈
      S.photonSupport ⊓ S.electronicSupport L ⊓ S.numberSupport M :=
  ⟨⟨C.photon_electronic L _ (C.photon_number M v hv), C.electronic_range L _⟩,
    C.number_electronic L M _ (C.number_range M v)⟩

theorem exists_localVector (C : SpatialCutoffSupport S Z P) (L M : ℕ)
    (v : SpatialPhotonL2 I K) (hv : v ∈ S.photonSupport) :
    ∃ w, S.embedding L M w = (Z L).operator ((P M).compLpL 2 volume v) := by
  have h := C.cut_mem L M v hv
  change (Z L).operator ((P M).compLpL 2 volume v) ∈
    (↑(S.photonSupport ⊓ S.electronicSupport L ⊓ S.numberSupport M) :
      Set (SpatialPhotonL2 I K)) at h
  rw [← S.range_eq L M] at h
  exact h

def localVector (C : SpatialCutoffSupport S Z P) (L M : ℕ)
    (v : SpatialPhotonL2 I K) (hv : v ∈ S.photonSupport) : Hlocal :=
  (C.exists_localVector L M v hv).choose

theorem localVector_identity (C : SpatialCutoffSupport S Z P) (L M : ℕ)
    (v : SpatialPhotonL2 I K) (hv : v ∈ S.photonSupport) :
    S.embedding L M (C.localVector L M v hv) =
      (Z L).operator ((P M).compLpL 2 volume v) :=
  (C.exists_localVector L M v hv).choose_spec

variable [CompleteSpace K]

theorem localVector_finite (C : SpatialCutoffSupport S Z P) (L M : ℕ)
    (hR : ∀ v w, (v, w) ∈ R.graph → (P M v, P M w) ∈ R.graph)
    (u : SpatialFreeVector (I := I) R) (hu : u.value ∈ S.photonSupport) :
    (S.spectrum L M).FiniteEnergy (C.localVector L M u.value hu) :=
  (S.free_form L M _ ((Z L).cutVector (P M) hR u)
    (C.localVector_identity L M u.value hu)).1

theorem localVector_form (C : SpatialCutoffSupport S Z P) (L M : ℕ)
    (hR : ∀ v w, (v, w) ∈ R.graph → (P M v, P M w) ∈ R.graph)
    (u : SpatialFreeVector (I := I) R) (hu : u.value ∈ S.photonSupport) :
    (S.spectrum L M).form (C.localVector L M u.value hu) =
      ((Z L).cutVector (P M) hR u).form :=
  (S.free_form L M _ ((Z L).cutVector (P M) hR u)
    (C.localVector_identity L M u.value hu)).2

theorem localVector_form_le (C : SpatialCutoffSupport S Z P) (L M : ℕ)
    (hP : ∀ v, ‖P M v‖ ≤ ‖v‖)
    (hR : ∀ v w, (v, w) ∈ R.graph → (P M v, P M w) ∈ R.graph)
    (u : SpatialFreeVector (I := I) R) (hu : u.value ∈ S.photonSupport) :
    (S.spectrum L M).form (C.localVector L M u.value hu) ≤
      2 * u.form + (2 * Fintype.card I * (Z L).derivativeBound ^ 2) * ‖u.value‖ ^ 2 := by
  rw [C.localVector_form L M hR u hu]
  exact (Z L).cutVector_form_le (P M) hP hR u

theorem localVector_form_summable (C : SpatialCutoffSupport S Z P) (L M : ℕ)
    (hP : ∀ v, ‖P M v‖ ≤ ‖v‖)
    (hR : ∀ v w, (v, w) ∈ R.graph → (P M v, P M w) ∈ R.graph)
    (u : ℕ → SpatialFreeVector (I := I) R) (hu : ∀ k, (u k).value ∈ S.photonSupport)
    (hs : Summable (fun k => (u k).form)) :
    Summable (fun k => (S.spectrum L M).form (C.localVector L M (u k).value (hu k))) := by
  have hm : Summable (fun k => ‖(u k).value‖ ^ 2) :=
    hs.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => (u k).mass_le_form)
  apply ((hs.mul_left 2).add
    (hm.mul_left (2 * Fintype.card I * (Z L).derivativeBound ^ 2))).of_nonneg_of_le
  · intro k
    rw [C.localVector_form L M hR]
    exact SpatialFreeVector.form_nonneg _
  · intro k
    exact C.localVector_form_le L M hP hR (u k) (hu k)

/-- The local form sum follows from the source energy and trace mass.
There is no dependence on the number cutoff. -/
theorem localVector_form_tsum_le (C : SpatialCutoffSupport S Z P) (L M : ℕ)
    (hP : ∀ v, ‖P M v‖ ≤ ‖v‖)
    (hR : ∀ v w, (v, w) ∈ R.graph → (P M v, P M w) ∈ R.graph)
    (u : ℕ → SpatialFreeVector (I := I) R) (hu : ∀ k, (u k).value ∈ S.photonSupport)
    (hs : Summable (fun k => (u k).form)) {E mass : ℝ}
    (hE : ∑' k, (u k).form ≤ E) (hmass : ∑' k, ‖(u k).value‖ ^ 2 ≤ mass) :
    ∑' k, (S.spectrum L M).form (C.localVector L M (u k).value (hu k)) ≤
      2 * E + (2 * Fintype.card I * (Z L).derivativeBound ^ 2) * mass := by
  have hm : Summable (fun k => ‖(u k).value‖ ^ 2) :=
    hs.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => (u k).mass_le_form)
  calc
    _ ≤ ∑' k, (2 * (u k).form +
        (2 * Fintype.card I * (Z L).derivativeBound ^ 2) * ‖(u k).value‖ ^ 2) :=
      Summable.tsum_le_tsum (fun k => C.localVector_form_le L M hP hR (u k) (hu k))
        (C.localVector_form_summable L M hP hR u hu hs)
        ((hs.mul_left 2).add (hm.mul_left _))
    _ = 2 * (∑' k, (u k).form) +
        (2 * Fintype.card I * (Z L).derivativeBound ^ 2) * (∑' k, ‖(u k).value‖ ^ 2) := by
      rw [Summable.tsum_add (hs.mul_left 2) (hm.mul_left _), tsum_mul_left, tsum_mul_left]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hE (by norm_num))
      (mul_le_mul_of_nonneg_left hmass (by positivity))

end SpatialCutoffSupport

end GptLean.PhotonLocalization
