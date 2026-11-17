import GptLean.PhotonLocalizationPhysicalEndpoint
import GptLean.PhotonLocalizationFreeEnergy

/-!
The coarse closure data for a single normal Fock channel.

The physical compactness theorem is applied to the original spectral
vectors and their actual Kraus outputs. The uniform rough PF bound is
derived from the two universal PF/free form comparisons, the unchanged
electronic kinetic form and one-photon radiation control. No local
precompactness or rough PF bound is a constructor input.
-/

namespace GptLean.PhotonLocalization

open MeasureTheory Filter Topology
open PhotonLocalizationChannel PhotonLocalizationFockChannel
open PhotonLocalizationFormBounds PhotonLocalizationFreeEnergy
open scoped ENNReal

section Bounds

variable {H h X Q : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {A : Gaussian.RankOneData H X} {Tr : RemovalState.PositiveTraceData X}
  {F : FockFactorization h H}

/-- PF energy control gives the free-form bound on the actual channel.
The one-photon form inequality is lifted through finite sectors, Kraus
coordinates and the normal source series by `channel_bound`. -/
theorem channel_free_bound_of_onePhoton
    (normal : NormalTraceData A) (forms : FockFormCalculus A Tr F Q)
    (hpositive : A.positive ⊆ Tr.positive) (radiation : Q)
    (free kinetic : RemovalState.PositiveForm Tr)
    (hfree : ∀ y ∈ A.positive, free.expectation y =
      ENNReal.ofReal (A.trace y) + kinetic.expectation y +
        (forms.observable radiation).expectation y)
    (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (W : ℕ → H →L[ℂ] H)
    (hWtrace : ∀ k v, (kinetic.truncation k (A.rankOne v) : ℂ) = inner ℂ v (W k v))
    (hW : ∀ k v a, F.factor j (W k v) a = W k (F.factor j v a))
    (pf : X → ℝ≥0∞) {a C E : ℝ} (ha : 0 ≤ a)
    (hcomparison : ∀ y ∈ A.positive, free.expectation y ≤
      ENNReal.ofReal a * (pf y + ENNReal.ofReal (A.trace y)))
    (hone : ∀ v, forms.value radiation (retainedMap j v) ≤
      ENNReal.ofReal C * forms.value radiation v)
    {x : X} (hx : x ∈ normal.states) (hE : pf x ≤ ENNReal.ofReal E) :
    free.expectation (normal.extend (F.factor j) x) ≤
      ENNReal.ofReal (max 1 C * (a * (max E 0 + 1))) := by
  apply free_energy_bound normal free kinetic (forms.observable radiation) hfree
    (F.factor j) W hWtrace hW hx.1
  · exact forms.channel_bound normal hpositive j radiation radiation hone hx.1
  · exact source_free_bound_of_pf normal free pf ha (le_max_right E 0)
      hcomparison hx (hE.trans (ENNReal.ofReal_le_ofReal (le_max_left E 0)))

/-- The reverse universal form comparison converts the derived free
bound to a radius-independent PF bound. -/
theorem channel_pf_bound_of_free
    (normal : NormalTraceData A) (free : RemovalState.PositiveForm Tr)
    (pf : X → ℝ≥0∞) {b bound : ℝ} (hb : 0 ≤ b)
    (hcomparison : ∀ y ∈ A.positive, pf y ≤ ENNReal.ofReal b * free.expectation y)
    (U : KrausIsometry H) {x : X} (hx : x ∈ A.positive)
    (hfree : free.expectation (normal.extend U x) ≤ ENNReal.ofReal bound) :
    pf (normal.extend U x) ≤ ENNReal.ofReal (b * bound) := by
  calc
    _ ≤ ENNReal.ofReal b * free.expectation (normal.extend U x) :=
      hcomparison _ (normal.positive U hx)
    _ ≤ ENNReal.ofReal b * ENNReal.ofReal bound := mul_le_mul_right hfree _
    _ = _ := (ENNReal.ofReal_mul hb).symm

end Bounds

section Coarse

variable {N : ℕ} {K Hlocal h X Q Test : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup Hlocal] [InnerProductSpace ℂ Hlocal] [CompleteSpace Hlocal]
  [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {μ : Measure ElectronicPosition}
  {R : K →ₗ.[ℂ] K}

/-- Coarse closure data assembled from the physical normal channel and
one-photon form orders. The two form comparisons are uniform over all
positive states. Local spectra, graph identifications and electronic
density marginals refer to this same realization.

Electronic tightness is witnessed by norm convergence of the original
densities, exactly what the constrained-search closure argument supplies.
The source spectral families and the output compactness are constructed
inside this definition. -/
noncomputable def CoarseData.ofChannelSources
    (D : PhotonLoss.LocalizationData X) (T : PhotonLoss.TraceData D Test)
    (A : Gaussian.RankOneData (SpatialPhotonL2 (Fin N × Fin 3) K) X)
    (normal : NormalTraceData A) (functional : NormalFunctionalData A)
    (Tr : RemovalState.PositiveTraceData X) (hpositive : A.positive ⊆ Tr.positive)
    (F : FockFactorization h (SpatialPhotonL2 (Fin N × Fin 3) K))
    (forms : FockFormCalculus A Tr F Q) (radiation number : Q)
    (j : ℕ → h →ₗᵢ[ℂ] WithLp 2 (h × h))
    (hstates : D.states ⊆ normal.states)
    (hchannel : ∀ m x, D.localize m x = normal.extend (F.factor (j m)) x)
    (free kinetic : RemovalState.PositiveForm Tr)
    (hfree : ∀ y ∈ A.positive, free.expectation y =
      ENNReal.ofReal (A.trace y) + kinetic.expectation y +
        (forms.observable radiation).expectation y)
    (W : ℕ → SpatialPhotonL2 (Fin N × Fin 3) K →L[ℂ]
      SpatialPhotonL2 (Fin N × Fin 3) K)
    (hWtrace : ∀ k v, (kinetic.truncation k (A.rankOne v) : ℂ) = inner ℂ v (W k v))
    (hW : ∀ m k v a, F.factor (j m) (W k v) a = W k (F.factor (j m) v a))
    {a b Crad : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hforward : ∀ y ∈ A.positive, free.expectation y ≤
      ENNReal.ofReal a * (T.energy y + ENNReal.ofReal (A.trace y)))
    (hreverse : ∀ y ∈ A.positive, T.energy y ≤ ENNReal.ofReal b * free.expectation y)
    (hrad : ∀ m v, forms.value radiation (retainedMap (j m) v) ≤
      ENNReal.ofReal Crad * forms.value radiation v)
    (Cnumber : ℕ → ℝ) (hCnumber : ∀ m, 0 ≤ Cnumber m)
    (hnumber : ∀ m v, forms.value number (retainedMap (j m) v) ≤
      ENNReal.ofReal (Cnumber m) * forms.value radiation v)
    (S : ℕ → SupportedFreeSpectrum (I := Fin N × Fin 3) R Hlocal)
    (sector : ℕ → K →L[ℂ] K)
    (hsector : ∀ k, IsStarProjection (sector k))
    (horthogonal : ∀ i k, i ≠ k → sector i * sector k = 0)
    (hR : ∀ k v w, (v, w) ∈ R.graph → (sector k v, sector k w) ∈ R.graph)
    (C : ∀ m, SpatialCutoffSupport (S m) physicalElectronicFamily (numberSectorCutoff sector))
    (hgraph : ∀ v, free.expectation (A.rankOne v) < ⊤ →
      ∃ u : SpatialFreeVector (I := Fin N × Fin 3) R, u.value = v ∧
        free.expectation (A.rankOne v) = ENNReal.ofReal u.form)
    (hsupport : ∀ m v k, F.factor (j m) v k ∈ (S m).photonSupport)
    (hsectorTrace : ∀ x ∈ normal.states, HasSum
      (fun k => (functional.repr x ((sector k).compLpL 2 volume)).re)
      (functional.repr x 1).re)
    (hnumberSeries : ∀ x ∈ normal.states, (forms.observable number).expectation x =
      ∑' k : ℕ, ENNReal.ofReal ((k : ℝ) *
        (functional.repr x ((sector k).compLpL 2 volume)).re))
    (density : X → Lp ℝ 1 μ) (position : X → Measure (Fin N → ElectronicPosition))
    [∀ x, IsFiniteMeasure (position x)]
    (hposition : ∀ x ∈ normal.states, ∀ f,
      (functional.repr x (positionObservable f)).re = ∫ z, f z ∂position x)
    (hintertwine : ∀ m f v k, F.factor (j m) (positionObservable f v) k =
      positionObservable f (F.factor (j m) v k))
    (hdensity : ∀ x ∈ normal.states, ElectronicDensityMeasure (position x) (density x)) :
    CoarseData D T where
  electronicTight u := ∃ ρ, Tendsto (fun n => density (u n)) atTop (𝓝 ρ)
  precompact u E hu hE htight m := by
    have hunormal : ∀ n, u n ∈ normal.states := fun n => hstates (hu n)
    choose v hv using fun n => normal.positive_decomposition (u n) (hunormal n).1
    obtain ⟨ρ, hρ⟩ := htight
    have hsource n : free.expectation (u n) ≤ ENNReal.ofReal (a * (max E 0 + 1)) :=
      source_free_bound_of_pf normal free T.energy ha (le_max_right E 0)
        hforward (hunormal n) ((hE n).trans (ENNReal.ofReal_le_ofReal (le_max_left E 0)))
    have hradiation n : (forms.observable radiation).expectation (u n) ≤
        free.expectation (u n) := by
      rw [hfree _ (hunormal n).1]
      exact le_add_left le_rfl
    have hn n : (forms.observable number).expectation
        (normal.extend (F.factor (j m)) (u n)) ≤
        ENNReal.ofReal (Cnumber m * (a * (max E 0 + 1))) := by
      calc
        _ ≤ ENNReal.ofReal (Cnumber m) * (forms.observable radiation).expectation (u n) :=
          forms.channel_bound normal hpositive (j m) number radiation (hnumber m) (hunormal n).1
        _ ≤ ENNReal.ofReal (Cnumber m) * ENNReal.ofReal (a * (max E 0 + 1)) :=
          mul_le_mul_right ((hradiation n).trans (hsource n)) _
        _ = _ := (ENNReal.ofReal_mul (hCnumber m)).symm
    have htb := channelSources_totallyBounded (S m) sector hsector horthogonal hR (C m)
      A normal functional Tr hpositive free (forms.observable number).expectation hgraph
      (F.factor (j m)) u hunormal v hv (hsupport m)
      (show 0 ≤ max 1 Crad * (a * (max E 0 + 1)) by positivity)
      (mul_nonneg (hCnumber m) (mul_nonneg ha (by positivity)))
      (fun n => channel_free_bound_of_onePhoton normal forms hpositive radiation free kinetic
        hfree (j m) W hWtrace (hW m) T.energy ha hforward (hrad m) (hunormal n) (hE n))
      hn
      (fun n => hsectorTrace _ (normal.preserves_states _ (hunormal n)))
      (fun n => hnumberSeries _ (normal.preserves_states _ (hunormal n)))
      (fun n => density (u n)) (fun n => position (u n))
      (fun n => hposition _ (hunormal n)) (hintertwine m)
      (fun n => hdensity _ (hunormal n)) hρ
    simpa only [hchannel] using htb
  rough E := b * (max 1 Crad * (a * (max E 0 + 1)))
  rough_bound E m x hx hE := by
    have hn : x ∈ normal.states := hstates hx
    rw [hchannel]
    exact channel_pf_bound_of_free normal free T.energy hb hreverse _ hn.1
      (channel_free_bound_of_onePhoton normal forms hpositive radiation free kinetic
        hfree (j m) W hWtrace (hW m) T.energy ha hforward (hrad m) hn hE)

end Coarse

end GptLean.PhotonLocalization
