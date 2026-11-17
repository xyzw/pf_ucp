import GptLean.PhysicalFockKernelField
import GptLean.PhysicalFockSpatialField

/-!
Adjoint pairings and symmetry of the actual fields on the radiation graph.

The proof sums adjacent-sector adjointness. Both full outputs have already
been constructed in Fock space, so their scalar products are absolutely
summable and the shift of the photon-number index is justified directly.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

private theorem shifted_series_inner
    {K : ℕ → Type*} [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
    (u v c a : lp K 2) (hc : c 0 = 0)
    (h : ∀ n, ⟪c (n + 1), v (n + 1)⟫_ℂ = ⟪u n, a n⟫_ℂ) :
    ⟪c, v⟫_ℂ = ⟪u, a⟫_ℂ := by
  have hs : Summable (fun n : ℕ => ⟪c n, v n⟫_ℂ) :=
    (lp.hasSum_inner (𝕜 := ℂ) c v).summable
  have ht : (∑' n : ℕ, ⟪c n, v n⟫_ℂ) =
      ⟪c 0, v 0⟫_ℂ + ∑' n : ℕ, ⟪c (n + 1), v (n + 1)⟫_ℂ :=
    hs.tsum_eq_zero_add
  have hz : ⟪c 0, v 0⟫_ℂ = 0 := hc ▸ inner_zero_left _
  calc
    _ = ∑' n : ℕ, ⟪c n, v n⟫_ℂ := lp.inner_eq_tsum c v
    _ = ∑' n : ℕ, ⟪c (n + 1), v (n + 1)⟫_ℂ := by rw [ht, hz, zero_add]
    _ = ∑' n : ℕ, ⟪u n, a n⟫_ℂ := tsum_congr h
    _ = _ := (lp.inner_eq_tsum u a).symm

private theorem pairing_symm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {a b c d : H} (h : ⟪a, b⟫_ℂ = ⟪c, d⟫_ℂ) :
    ⟪b, a⟫_ℂ = ⟪d, c⟫_ℂ := by
  have he := congrArg (starRingEnd ℂ) h
  simpa only [inner_conj_symm] using he

private theorem pairing_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {a b c d u v : H} (h₁ : ⟪a, v⟫_ℂ = ⟪u, d⟫_ℂ)
    (h₂ : ⟪b, v⟫_ℂ = ⟪u, c⟫_ℂ) :
    ⟪a + b, v⟫_ℂ = ⟪u, c + d⟫_ℂ := by
  rw [inner_add_left, inner_add_right, h₁, h₂, add_comm]

private theorem l2_inner_eq_of_ae {X H : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b c d : Lp H 2 μ)
    (h : ∀ᵐ x ∂μ, ⟪a x, b x⟫_ℂ = ⟪c x, d x⟫_ℂ) : ⟪a, b⟫_ℂ = ⟪c, d⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_congr_ae h

theorem kernelCreation_annihilation_duality (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q r : RadiationGraphSpace) :
    ⟪kernelCreation C k q, radiationGraphInclusion r⟫_ℂ =
      ⟪radiationGraphInclusion q, kernelAnnihilation k r⟫_ℂ := by
  apply shifted_series_inner (radiationGraphInclusion q) (radiationGraphInclusion r)
    (kernelCreation C k q) (kernelAnnihilation k r) rfl
  intro n
  exact annihilationSector_duality photonMeasure n k.val.1
    (radiationGraphInclusion q n) (radiationGraphInclusion r (n + 1))

theorem kernelAnnihilation_creation_duality (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q r : RadiationGraphSpace) :
    ⟪kernelAnnihilation k q, radiationGraphInclusion r⟫_ℂ =
      ⟪radiationGraphInclusion q, kernelCreation C k r⟫_ℂ :=
  pairing_symm (kernelCreation_annihilation_duality C k r q).symm

/-- The Segal field is symmetric on the actual square-root radiation domain. -/
theorem kernelField_symmetric (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q r : RadiationGraphSpace) :
    ⟪kernelField C k q, radiationGraphInclusion r⟫_ℂ =
      ⟪radiationGraphInclusion q, kernelField C k r⟫_ℂ :=
  pairing_add (kernelAnnihilation_creation_duality C k q r)
    (kernelCreation_annihilation_duality C k q r)

section Spatial
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (C : CanonicalSectorCCR photonMeasure) (κ : X → WeightedPhotonKernel)
  (hκ : AEStronglyMeasurable κ μ) (M : ℝ)
  (hbound : ∀ᵐ x ∂μ, ‖κ x‖ ≤ M)

/-- Pointwise field symmetry passes to the actual electronic L² realization. -/
theorem spatialField_symmetric (u v : SpatialRadiationGraph μ) :
    ⟪spatialField μ C κ hκ M hbound u, spatialRadiationInclusion μ v⟫_ℂ =
      ⟪spatialRadiationInclusion μ u, spatialField μ C κ hκ M hbound v⟫_ℂ := by
  apply l2_inner_eq_of_ae (spatialField μ C κ hκ M hbound u)
    (spatialRadiationInclusion μ v) (spatialRadiationInclusion μ u)
    (spatialField μ C κ hκ M hbound v)
  have hu : spatialRadiationInclusion μ u =ᵐ[μ]
      fun x => radiationGraphInclusion (u x) := radiationGraphInclusion.coeFn_compLpL u
  have hv : spatialRadiationInclusion μ v =ᵐ[μ]
      fun x => radiationGraphInclusion (v x) := radiationGraphInclusion.coeFn_compLpL v
  filter_upwards [spatialField_ae μ C κ hκ M hbound u,
    spatialField_ae μ C κ hκ M hbound v, hu, hv] with x hfu hfv hiu hiv
  exact (congrArg₂ (fun a b : PhotonFock => ⟪a, b⟫_ℂ) hfu hiv).trans
    ((kernelField_symmetric C (κ x) (u x) (v x)).trans
      (congrArg₂ (fun a b : PhotonFock => ⟪a, b⟫_ℂ) hiu.symm hfv.symm))

end Spatial

end GptLean.PhysicalFock
