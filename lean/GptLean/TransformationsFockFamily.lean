import GptLean.TransformationsFockPointwise

/-!
Second quantization of a general family of sector unitaries.

A one-particle unitary `u` together with unitaries `Uₙ` of the full n-particle
product spaces is a *sector family* when every `Uₙ` commutes with the
coordinate permutations and `Uₙ₊₁ (f ⊗ ψ) = (u f) ⊗ (Uₙ ψ)` for tensor
insertion. The pointwise unitaries of `TransformationsFockPointwise` are one
example, and the polarization-mixing unitaries of `TransformationsFockMixing`
are another. For every sector family the restrictions to the symmetric
sectors define a Fock unitary `Γ` with `Γ a^#(f) Γ⁻¹ = a^#(u f)`. Inverses
and composites of sector families are sector families.

On the photon Fock space, suppose that `Uₙ` commutes with multiplication by
the square root of the n-photon dispersion, and `u` with multiplication by
`|k|^{1/2}`, in both directions. Then `Γ` preserves the radiation graph, maps
weighted kernels to weighted kernels, and transforms the Segal field
covariantly.
-/

noncomputable section

namespace GptLean.TransformationsFock

open MeasureTheory
open GptLean.PhysicalFock
open scoped ENNReal InnerProductSpace

section Family

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A one-particle unitary with compatible unitaries of the full n-particle
product spaces. -/
structure SectorFamily (μ : Measure Ω) [SigmaFinite μ] where
  one : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ
  sector : ∀ n, FullSector μ n ≃ₗᵢ[ℂ] FullSector μ n
  perm : ∀ n (π : Equiv.Perm (Fin n)) (u : FullSector μ n),
    sector n (permutation μ n π u) = permutation μ n π (sector n u)
  insert : ∀ n (f : Lp ℂ 2 μ) (u : FullSector μ n),
    sector (n + 1) (tensorInsertion μ n f u) = tensorInsertion μ n (one f) (sector n u)

namespace SectorFamily

variable {μ : Measure Ω} [SigmaFinite μ] (G : SectorFamily μ)

theorem symm_perm (n : ℕ) (π : Equiv.Perm (Fin n)) (u : FullSector μ n) :
    (G.sector n).symm (permutation μ n π u) = permutation μ n π ((G.sector n).symm u) := by
  apply (G.sector n).injective
  rw [LinearIsometryEquiv.apply_symm_apply, G.perm, LinearIsometryEquiv.apply_symm_apply]

theorem sector_mem {n : ℕ} {u : FullSector μ n} (hu : u ∈ symmetricSubspace μ n) :
    G.sector n u ∈ symmetricSubspace μ n := by
  intro π
  rw [← G.perm, hu π]

theorem sector_symm_mem {n : ℕ} {u : FullSector μ n} (hu : u ∈ symmetricSubspace μ n) :
    (G.sector n).symm u ∈ symmetricSubspace μ n := by
  intro π
  rw [← G.symm_perm, hu π]

/-- The sector unitaries commute with the projection onto symmetric wave functions. -/
theorem sector_starProjection (n : ℕ) (u : FullSector μ n) :
    (symmetricSubspace μ n).starProjection (G.sector n u) =
      G.sector n ((symmetricSubspace μ n).starProjection u) :=
  starProjection_unitary_commute (G.sector n) (symmetricSubspace μ n)
    (fun _ hx => G.sector_mem hx) (fun _ hx => G.sector_symm_mem hx) u

/-- The sector unitary restricted to the symmetric n-particle sector. -/
def symSector (n : ℕ) : Sector μ n ≃ₗᵢ[ℂ] Sector μ n :=
  restrictUnitary (G.sector n) (symmetricSubspace μ n) (fun _ hx => G.sector_mem hx)
    (fun _ hx => G.sector_symm_mem hx)

@[simp] theorem symSector_val (n : ℕ) (u : Sector μ n) :
    (G.symSector n u).val = G.sector n u.val := rfl

@[simp] theorem symSector_symm_val (n : ℕ) (u : Sector μ n) :
    ((G.symSector n).symm u).val = (G.sector n).symm u.val := rfl

/-- Creation is covariant: the transformed kernel creates the transformed vector. -/
theorem symSector_creationSector (n : ℕ) (f : Lp ℂ 2 μ) (u : Sector μ n) :
    G.symSector (n + 1) (creationSector μ n f u) =
      creationSector μ n (G.one f) (G.symSector n u) := by
  apply Subtype.ext
  rw [symSector_val, creationSector_val, creationSector_val, symSector_val,
    LinearIsometryEquiv.map_smul, ← sector_starProjection, G.insert]

/-- Annihilation is covariant, by adjointness and unitarity. -/
theorem symSector_annihilationSector (n : ℕ) (f : Lp ℂ 2 μ) (v : Sector μ (n + 1)) :
    G.symSector n (annihilationSector μ n f v) =
      annihilationSector μ n (G.one f) (G.symSector (n + 1) v) := by
  apply ext_inner_left ℂ
  intro w
  obtain ⟨w, rfl⟩ := (G.symSector n).surjective w
  rw [← annihilationSector_duality, ← symSector_creationSector,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map,
    annihilationSector_duality]

/-- The second quantization of a sector family, acting sector by sector. -/
def fock : Fock μ ≃ₗᵢ[ℂ] Fock μ := sectorwise fun n => G.symSector n

@[simp] theorem fock_apply (u : Fock μ) (n : ℕ) : G.fock u n = G.symSector n (u n) := rfl

@[simp] theorem fock_symm_apply (u : Fock μ) (n : ℕ) :
    G.fock.symm u n = (G.symSector n).symm (u n) := rfl

/-- The inverse sector family. -/
def symm : SectorFamily μ where
  one := G.one.symm
  sector n := (G.sector n).symm
  perm := G.symm_perm
  insert n f u := by
    apply (G.sector (n + 1)).injective
    rw [LinearIsometryEquiv.apply_symm_apply, G.insert, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.apply_symm_apply]

@[simp] theorem symm_one (f : Lp ℂ 2 μ) : G.symm.one f = G.one.symm f := rfl

@[simp] theorem symm_sector (n : ℕ) (u : FullSector μ n) :
    G.symm.sector n u = (G.sector n).symm u := rfl

/-- The second quantization of the inverse family is the inverse unitary. -/
theorem symm_fock (u : Fock μ) : G.symm.fock u = G.fock.symm u := by
  apply lp.ext
  funext n
  exact Subtype.ext rfl

/-- The composite family, first `G` and then `H`. -/
def trans (H : SectorFamily μ) : SectorFamily μ where
  one := G.one.trans H.one
  sector n := (G.sector n).trans (H.sector n)
  perm n π u := by
    change H.sector n (G.sector n (permutation μ n π u)) =
      permutation μ n π (H.sector n (G.sector n u))
    rw [G.perm, H.perm]
  insert n f u := by
    change H.sector (n + 1) (G.sector (n + 1) (tensorInsertion μ n f u)) =
      tensorInsertion μ n (H.one (G.one f)) (H.sector n (G.sector n u))
    rw [G.insert, H.insert]

@[simp] theorem trans_one (H : SectorFamily μ) (f : Lp ℂ 2 μ) :
    (G.trans H).one f = H.one (G.one f) := rfl

@[simp] theorem trans_sector (H : SectorFamily μ) (n : ℕ) (u : FullSector μ n) :
    (G.trans H).sector n u = H.sector n (G.sector n u) := rfl

/-- The second quantization of a composite is the composite of the second
quantizations. -/
theorem trans_fock (H : SectorFamily μ) (u : Fock μ) :
    (G.trans H).fock u = H.fock (G.fock u) := by
  apply lp.ext
  funext n
  exact Subtype.ext rfl

end SectorFamily

/-- A pointwise unitary is a sector family. -/
def PointwiseUnitary.family {μ : Measure Ω} [SigmaFinite μ] (U : PointwiseUnitary μ) :
    SectorFamily μ where
  one := oneParticle U
  sector := sectorMap U
  perm := sectorMap_permutation U
  insert := sectorMap_tensorInsertion U

theorem PointwiseUnitary.family_fock {μ : Measure Ω} [SigmaFinite μ] (U : PointwiseUnitary μ)
    (u : Fock μ) : U.family.fock u = fockMap U u := rfl

end Family

section Photon

namespace SectorFamily

/-- The sector unitaries commute with the square root of the n-photon
dispersion, and the one-photon unitary with `|k|^{1/2}`, in both directions. -/
structure Dispersive (G : SectorFamily photonMeasure) : Prop where
  sector : ∀ n (f g : FullSector photonMeasure n),
    (∀ᵐ k ∂SectorMeasure photonMeasure n,
      f k = (Real.sqrt (sectorDispersion n k) : ℂ) * g k) →
    ∀ᵐ k ∂SectorMeasure photonMeasure n,
      G.sector n f k = (Real.sqrt (sectorDispersion n k) : ℂ) * G.sector n g k
  sector_symm : ∀ n (f g : FullSector photonMeasure n),
    (∀ᵐ k ∂SectorMeasure photonMeasure n,
      f k = (Real.sqrt (sectorDispersion n k) : ℂ) * g k) →
    ∀ᵐ k ∂SectorMeasure photonMeasure n,
      (G.sector n).symm f k = (Real.sqrt (sectorDispersion n k) : ℂ) * (G.sector n).symm g k
  one : ∀ f g : Lp ℂ 2 photonMeasure,
    (∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p) →
    ∀ᵐ p ∂photonMeasure, G.one f p = (Real.sqrt ‖p.1‖ : ℂ) * G.one g p
  one_symm : ∀ f g : Lp ℂ 2 photonMeasure,
    (∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p) →
    ∀ᵐ p ∂photonMeasure, G.one.symm f p = (Real.sqrt ‖p.1‖ : ℂ) * G.one.symm g p

variable (G H : SectorFamily photonMeasure) (hG : G.Dispersive) (hH : H.Dispersive)

include hG in
theorem dispersive_symm : G.symm.Dispersive :=
  ⟨hG.sector_symm, hG.sector, hG.one_symm, hG.one⟩

include hG hH in
theorem dispersive_trans : (G.trans H).Dispersive :=
  ⟨fun n f g h => hH.sector n _ _ (hG.sector n f g h),
    fun n f g h => hG.sector_symm n _ _ (hH.sector_symm n f g h),
    fun f g h => hH.one _ _ (hG.one f g h),
    fun f g h => hG.one_symm _ _ (hH.one_symm f g h)⟩

include hG in
theorem fock_graph {u v : PhotonFock} (h : (u, v) ∈ radiationRoot.graph) :
    (G.fock u, G.fock v) ∈ radiationRoot.graph := by
  rw [radiationRoot_graph_iff] at h ⊢
  intro n
  exact hG.sector n _ _ (h n)

include hG in
theorem fock_symm_graph {u v : PhotonFock} (h : (u, v) ∈ radiationRoot.graph) :
    (G.fock.symm u, G.fock.symm v) ∈ radiationRoot.graph := by
  rw [radiationRoot_graph_iff] at h ⊢
  intro n
  exact hG.sector_symm n _ _ (h n)

/-- The Fock unitary restricted to the closed radiation graph. -/
def radiationGraph : RadiationGraphSpace ≃ₗᵢ[ℂ] RadiationGraphSpace :=
  restrictUnitary (prodUnitary G.fock) radiationRoot.graph
    (fun x hx => by
      obtain ⟨u, v⟩ := x
      exact G.fock_graph hG hx)
    (fun x hx => by
      obtain ⟨u, v⟩ := x
      exact G.fock_symm_graph hG hx)

theorem radiationGraphInclusion_radiationGraph (q : RadiationGraphSpace) :
    radiationGraphInclusion (G.radiationGraph hG q) = G.fock (radiationGraphInclusion q) :=
  rfl

theorem radiationGraphDerivative_radiationGraph (q : RadiationGraphSpace) :
    radiationGraphDerivative (G.radiationGraph hG q) = G.fock (radiationGraphDerivative q) :=
  rfl

/-- A dispersive family maps weighted kernels to weighted kernels. -/
def kernel : WeightedPhotonKernel ≃ₗᵢ[ℂ] WeightedPhotonKernel :=
  restrictUnitary (prodUnitary G.one) weightedKernelSubspace
    (fun x hx => hG.one x.1 x.2 hx) (fun x hx => hG.one_symm x.1 x.2 hx)

@[simp] theorem kernel_fst (k : WeightedPhotonKernel) :
    (G.kernel hG k).val.1 = G.one k.val.1 := rfl

@[simp] theorem kernel_snd (k : WeightedPhotonKernel) :
    (G.kernel hG k).val.2 = G.one k.val.2 := rfl

/-- Graph-domain annihilation is covariant. -/
theorem kernelAnnihilation_kernel (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelAnnihilation (G.kernel hG k) (G.radiationGraph hG q) =
      G.fock (kernelAnnihilation k q) := by
  apply lp.ext
  funext n
  change annihilationSector photonMeasure n (G.kernel hG k).val.1
      (radiationGraphInclusion (G.radiationGraph hG q) (n + 1)) =
    G.symSector n (annihilationSector photonMeasure n k.val.1
      (radiationGraphInclusion q (n + 1)))
  rw [kernel_fst, radiationGraphInclusion_radiationGraph, fock_apply,
    symSector_annihilationSector]

/-- Graph-domain creation is covariant. -/
theorem kernelCreation_kernel (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelCreation C (G.kernel hG k) (G.radiationGraph hG q) =
      G.fock (kernelCreation C k q) := by
  apply lp.ext
  funext n
  cases n with
  | zero => exact (map_zero (G.symSector 0)).symm
  | succ n =>
    change creationSector photonMeasure n (G.kernel hG k).val.1
        (radiationGraphInclusion (G.radiationGraph hG q) n) =
      G.symSector (n + 1) (creationSector photonMeasure n k.val.1
        (radiationGraphInclusion q n))
    rw [kernel_fst, radiationGraphInclusion_radiationGraph, fock_apply,
      symSector_creationSector]

/-- The Segal field is covariant under a dispersive sector family. -/
theorem kernelField_kernel (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelField C (G.kernel hG k) (G.radiationGraph hG q) = G.fock (kernelField C k q) := by
  simp only [kernelField, add_apply, kernelAnnihilation_kernel,
    kernelCreation_kernel, LinearIsometryEquiv.map_add]

/-- The radiation-graph map of the inverse family is the inverse map. -/
theorem symm_radiationGraph (q : RadiationGraphSpace) :
    G.symm.radiationGraph (G.dispersive_symm hG) q = (G.radiationGraph hG).symm q := by
  apply Subtype.ext
  apply Prod.ext
  · exact G.symm_fock _
  · exact G.symm_fock _

end SectorFamily

/-- A length-preserving pointwise unitary is a dispersive sector family. -/
theorem PointwiseUnitary.family_dispersive (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) : U.family.Dispersive :=
  ⟨fun n _ _ h => oneParticle_mul_ae (U.power n) (fun k => (Real.sqrt (sectorDispersion n k) : ℂ))
      (fun k => congrArg (fun t : ℝ => (Real.sqrt t : ℂ)) (power_sectorDispersion U hU n k)) h,
    fun n _ _ h => oneParticle_mul_ae (U.power n).symm
      (fun k => (Real.sqrt (sectorDispersion n k) : ℂ))
      (fun k => congrArg (fun t : ℝ => (Real.sqrt t : ℂ))
        ((U.power n).symm_invariant (sectorDispersion n) (power_sectorDispersion U hU n) k)) h,
    fun _ _ h => oneParticle_mul_ae U (fun p => (Real.sqrt ‖p.1‖ : ℂ))
      (fun p => congrArg (fun t : ℝ => (Real.sqrt t : ℂ)) (hU p)) h,
    fun _ _ h => oneParticle_mul_ae U.symm (fun p => (Real.sqrt ‖p.1‖ : ℂ))
      (fun p => congrArg (fun t : ℝ => (Real.sqrt t : ℂ))
        (U.symm_invariant (fun p => ‖p.1‖) hU p)) h⟩

end Photon

end GptLean.TransformationsFock
