import GptLean.PhysicalFockFieldGraph
import GptLean.PhysicalFockFiniteOperators
import GptLean.PhysicalFockMomentumSupport
import GptLean.Repair.CovariantProduct

/-!
The auxiliary one-photon tag in Steps 2 and 6 of photonic
representability. An orthonormal family of actual one-photon sectors
embeds the entire tag Hilbert space into a single photon-number sector.
The construction preserves its connection and metric, has zero Segal
field expectation, and has uniformly bounded radiation energy when the
chosen modes have uniformly bounded momentum support.

Existence of the orthonormal modes in the chosen annulus is not asserted
here. No field expectation or radiation estimate is assumed about them.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Representability.OnePhotonTag

open MeasureTheory Filter Topology GptLean.PhysicalFock
open scoped ENNReal InnerProductSpace

variable {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Synthesis of the tag coefficients in actual one-photon modes. -/
def sectorEmbedding (b : HilbertBasis ι ℂ V)
    (ξ : ι → Sector photonMeasure 1) (hξ : Orthonormal ℂ ξ) :
    V →ₗᵢ[ℂ] Sector photonMeasure 1 :=
  hξ.orthogonalFamily.linearIsometry.comp b.repr.toLinearIsometry

/-- The auxiliary tag occupies exactly one photon-number sector. -/
def embedding (b : HilbertBasis ι ℂ V)
    (ξ : ι → Sector photonMeasure 1) (hξ : Orthonormal ℂ ξ) :
    V →ₗᵢ[ℂ] PhotonFock where
  toLinearMap := (lp.singleContinuousLinearMap ℂ (Sector photonMeasure) 2 1).toLinearMap.comp
    (sectorEmbedding b ξ hξ).toLinearMap
  norm_map' v := by
    change ‖lp.single 2 1 (sectorEmbedding b ξ hξ v)‖ = ‖v‖
    rw [lp.norm_single (by norm_num), (sectorEmbedding b ξ hξ).norm_map]

theorem embedding_eq_single (b : HilbertBasis ι ℂ V)
    (ξ : ι → Sector photonMeasure 1) (hξ : Orthonormal ℂ ξ) (v : V) :
    embedding b ξ hξ v = lp.single 2 1 (sectorEmbedding b ξ hξ v) := rfl

@[simp] theorem embedding_norm (b : HilbertBasis ι ℂ V)
    (ξ : ι → Sector photonMeasure 1) (hξ : Orthonormal ℂ ξ) (v : V) :
    ‖embedding b ξ hξ v‖ = ‖v‖ := (embedding b ξ hξ).norm_map v

@[simp] theorem embedding_inner (b : HilbertBasis ι ℂ V)
    (ξ : ι → Sector photonMeasure 1) (hξ : Orthonormal ℂ ξ) (v w : V) :
    ⟪embedding b ξ hξ v, embedding b ξ hξ w⟫_ℂ = ⟪v, w⟫_ℂ :=
  (embedding b ξ hξ).inner_map_map v w

theorem sectorEmbedding_hasSum (b : HilbertBasis ι ℂ V)
    (ξ : ι → Sector photonMeasure 1) (hξ : Orthonormal ℂ ξ) (v : V) :
    HasSum (fun i => ⟪b i, v⟫_ℂ • ξ i) (sectorEmbedding b ξ hξ v) := by
  simpa only [sectorEmbedding, LinearIsometry.comp_apply, b.repr_apply_apply,
    LinearIsometry.toSpanSingleton_apply] using!
    hξ.orthogonalFamily.hasSum_linearIsometry (b.repr v)

theorem embedding_hasSum (b : HilbertBasis ι ℂ V)
    (ξ : ι → Sector photonMeasure 1) (hξ : Orthonormal ℂ ξ) (v : V) :
    HasSum (fun i => ⟪b i, v⟫_ℂ • lp.single 2 1 (ξ i)) (embedding b ξ hξ v) := by
  simpa only [map_smul, lp.singleContinuousLinearMap_apply, embedding_eq_single] using
    (lp.singleContinuousLinearMap ℂ (Sector photonMeasure) 2 1).hasSum
      (sectorEmbedding_hasSum b ξ hξ v)

/-- Fixed photon number forces every ordinary Segal field expectation to vanish. -/
theorem single_field_expectation_zero (u : Sector photonMeasure 1)
    (f : Lp ℂ 2 photonMeasure) (w : PhotonFock)
    (hw : SegalGraph photonMeasure f (lp.single 2 1 u) w) :
    ⟪lp.single 2 1 u, w⟫_ℂ = 0 := by
  rw [lp.inner_single_left, hw 1]
  change ⟪u, annihilationSector photonMeasure 1 f ((lp.single 2 1 u) 2) +
    creationSector photonMeasure 0 f ((lp.single 2 1 u) 0)⟫_ℂ = 0
  simp only [lp.single_apply_ne _ _ _ (by decide : (2 : ℕ) ≠ 1),
    lp.single_apply_ne _ _ _ (by decide : (0 : ℕ) ≠ 1), map_zero, add_zero,
    inner_zero_right]

theorem embedding_field_expectation_zero (b : HilbertBasis ι ℂ V)
    (ξ : ι → Sector photonMeasure 1) (hξ : Orthonormal ℂ ξ) (v : V)
    (f : Lp ℂ 2 photonMeasure) (w : PhotonFock)
    (hw : SegalGraph photonMeasure f (embedding b ξ hξ v) w) :
    ⟪embedding b ξ hξ v, w⟫_ℂ = 0 :=
  single_field_expectation_zero _ f w hw

/-- The explicit field action is a sum of its zero- and two-photon sectors. -/
def fieldValue (f : Lp ℂ 2 photonMeasure) (u : Sector photonMeasure 1) : PhotonFock :=
  lp.single 2 0 (annihilationSector photonMeasure 0 f u) +
    lp.single 2 2 (creationSector photonMeasure 1 f u)

theorem fieldValue_graph (f : Lp ℂ 2 photonMeasure) (u : Sector photonMeasure 1) :
    SegalGraph photonMeasure f (lp.single 2 1 u) (fieldValue f u) := by
  intro n
  rcases n with _ | _ | n
  · simp [fieldValue, segalCoordinate, lp.evalCLM]
  · simp [fieldValue, segalCoordinate, lp.evalCLM]
  · by_cases hn : n = 0
    · subst n
      simp [fieldValue, segalCoordinate, lp.evalCLM]
    · have hn1 : n + 1 ≠ 1 := by omega
      have hn2 : n + 2 ≠ 2 := by omega
      have hn3 : n + 3 ≠ 1 := by omega
      simp [fieldValue, segalCoordinate, lp.evalCLM, hn2, Pi.single_eq_of_ne hn1]

/-- Momentum support of each chosen mode passes to the convergent tag series. -/
theorem sectorEmbedding_supported (b : HilbertBasis ι ℂ V)
    (ξ : ι → Sector photonMeasure 1) (hξ : Orthonormal ℂ ξ)
    (s : Set PhotonMode)
    (hs : ∀ i, (ξ i).val ∈ MomentumSupport.fullSupport photonMeasure 1 s) (v : V) :
    (sectorEmbedding b ξ hξ v).val ∈ MomentumSupport.fullSupport photonMeasure 1 s := by
  have hsum := (sectorInclusion photonMeasure 1).toContinuousLinearMap.hasSum
    (sectorEmbedding_hasSum b ξ hξ v)
  apply (MomentumSupport.fullSupport_closed photonMeasure 1 s).mem_of_tendsto hsum
  apply Eventually.of_forall
  intro t
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hs i)

/-- An upper momentum cutoff controls the actual radiation form in one sector. -/
theorem sectorRadiationForm_le (u : Sector photonMeasure 1) (R : ℝ)
    (hu : ∀ᵐ k ∂SectorMeasure photonMeasure 1, u.val k ≠ 0 → ‖(k 0).1‖ ≤ R) :
    sectorRadiationForm 1 u ≤ ENNReal.ofReal R * ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [← sector_mass_lintegral 1 u,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hu] with k hk
  by_cases hz : u.val k = 0
  · simp [hz]
  · apply mul_le_mul' ?_ le_rfl
    apply ENNReal.ofReal_le_ofReal
    simpa [sectorDispersion] using hk hz

theorem single_radiationForm (u : Sector photonMeasure 1) :
    radiationForm (lp.single 2 1 u) = sectorRadiationForm 1 u := by
  unfold radiationForm
  rw [tsum_eq_single 1]
  · rw [lp.single_apply_self]
  · intro n hn
    rw [lp.single_apply_ne _ _ _ hn, sectorRadiationForm_zero]

/-- The annular one-photon tag has a uniform energy bound even for an
infinite-dimensional source tag. Only the upper endpoint enters the bound. -/
theorem embedding_radiation_le (b : HilbertBasis ι ℂ V)
    (ξ : ι → Sector photonMeasure 1) (hξ : Orthonormal ℂ ξ)
    (s : Set PhotonMode) (R : ℝ) (hR : ∀ p ∈ s, ‖p.1‖ ≤ R)
    (hs : ∀ i, (ξ i).val ∈ MomentumSupport.fullSupport photonMeasure 1 s) (v : V) :
    radiationForm (embedding b ξ hξ v) ≤
      ENNReal.ofReal R * ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [embedding_eq_single, single_radiationForm,
    ← (sectorEmbedding b ξ hξ).norm_map v]
  apply sectorRadiationForm_le
  have hv := sectorEmbedding_supported b ξ hξ s hs v
  filter_upwards [hv] with k hk
  intro hne
  apply hR
  have hm : k ∈ MomentumSupport.productRegion 1 s := by
    by_contra hout
    exact hne (hk hout)
  exact hm 0

theorem embedding_metric {J : Type*} [Fintype J]
    (b : HilbertBasis ι ℂ V) (ξ : ι → Sector photonMeasure 1)
    (hξ : Orthonormal ℂ ξ) (g : J → V) :
    (∑ j, ‖embedding b ξ hξ (g j)‖ ^ 2) = ∑ j, ‖g j‖ ^ 2 := by
  simp only [embedding_norm]

variable [CompleteSpace V]

/-- The fixed one-photon embedding transports genuine compact-test weak derivatives. -/
theorem embedding_hasWeakH1Local {I : Type*} [Fintype I] [DecidableEq I]
    (b : HilbertBasis ι ℂ V) (ξ : ι → Sector photonMeasure 1) (hξ : Orthonormal ℂ ξ)
    {z : EuclideanSpace ℝ I → V} {dz : I → EuclideanSpace ℝ I → V}
    (hz : GptLean.SymmetricLift.HasWeakH1Local z dz) :
    GptLean.SymmetricLift.HasWeakH1Local (fun x => embedding b ξ hξ (z x))
      (fun i x => embedding b ξ hξ (dz i x)) :=
  GptLean.Repair.weakH1Local_map ((embedding b ξ hξ).toContinuousLinearMap.restrictScalars ℝ) hz

end GptLean.Representability.OnePhotonTag
