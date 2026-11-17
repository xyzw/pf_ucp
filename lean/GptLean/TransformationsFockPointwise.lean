import GptLean.PhysicalFockKernelField

/-!
Pointwise one-photon unitaries and their second quantization.

A measure-preserving measurable bijection `φ` of the one-photon space and a
measurable unimodular weight `m` act on L² by `(U f)(p) = m p * f (φ p)`.
On the n-fold product the same rule with the weight `∏ i, m (k i)` gives a
unitary which commutes with every coordinate permutation. It therefore
preserves the symmetric sector and commutes with the symmetric projection.
It intertwines tensor insertion, creation and annihilation with the
transformed one-photon kernel. Acting sector by sector gives the Fock
unitary. When `φ` preserves the length of the momentum, this unitary
preserves the radiation graph in both directions, and the graph-domain
annihilation, creation and field operators transform covariantly.
-/

noncomputable section

namespace GptLean.TransformationsFock

open MeasureTheory Filter
open GptLean.PhysicalFock
open scoped ENNReal InnerProductSpace

section Restriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A unitary which maps a subspace into itself, together with its inverse,
restricts to a unitary of the subspace. -/
def restrictUnitary (S : E ≃ₗᵢ[ℂ] E) (K : Submodule ℂ E) (h : ∀ x ∈ K, S x ∈ K)
    (h' : ∀ x ∈ K, S.symm x ∈ K) : K ≃ₗᵢ[ℂ] K where
  toFun x := ⟨S x, h x x.2⟩
  invFun x := ⟨S.symm x, h' x x.2⟩
  map_add' x y := Subtype.ext (map_add S (x : E) (y : E))
  map_smul' c x := Subtype.ext (map_smul S c (x : E))
  left_inv x := Subtype.ext (S.symm_apply_apply x)
  right_inv x := Subtype.ext (S.apply_symm_apply x)
  norm_map' x := S.norm_map x

@[simp] theorem restrictUnitary_val (S : E ≃ₗᵢ[ℂ] E) (K : Submodule ℂ E)
    (h : ∀ x ∈ K, S x ∈ K) (h' : ∀ x ∈ K, S.symm x ∈ K) (x : K) :
    (restrictUnitary S K h h' x).val = S x.val := rfl

@[simp] theorem restrictUnitary_symm_val (S : E ≃ₗᵢ[ℂ] E) (K : Submodule ℂ E)
    (h : ∀ x ∈ K, S x ∈ K) (h' : ∀ x ∈ K, S.symm x ∈ K) (x : K) :
    ((restrictUnitary S K h h').symm x).val = S.symm x.val := rfl

/-- The same unitary acting on both components of a pair. -/
def prodUnitary (S : E ≃ₗᵢ[ℂ] E) : (E × E) ≃ₗᵢ[ℂ] (E × E) where
  toFun x := (S x.1, S x.2)
  invFun x := (S.symm x.1, S.symm x.2)
  map_add' x y := Prod.ext (map_add S x.1 y.1) (map_add S x.2 y.2)
  map_smul' c x := Prod.ext (map_smul S c x.1) (map_smul S c x.2)
  left_inv x := Prod.ext (S.symm_apply_apply x.1) (S.symm_apply_apply x.2)
  right_inv x := Prod.ext (S.apply_symm_apply x.1) (S.apply_symm_apply x.2)
  norm_map' x := by
    change max ‖S x.1‖ ‖S x.2‖ = max ‖x.1‖ ‖x.2‖
    rw [S.norm_map, S.norm_map]

@[simp] theorem prodUnitary_apply (S : E ≃ₗᵢ[ℂ] E) (x : E × E) :
    prodUnitary S x = (S x.1, S x.2) := rfl

@[simp] theorem prodUnitary_symm_apply (S : E ≃ₗᵢ[ℂ] E) (x : E × E) :
    (prodUnitary S).symm x = (S.symm x.1, S.symm x.2) := rfl

end Restriction

/-- A unitary which preserves a closed subspace in both directions commutes with
the orthogonal projection onto it. -/
theorem starProjection_unitary_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : E ≃ₗᵢ[ℂ] E) (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (h : ∀ x ∈ K, S x ∈ K) (h' : ∀ x ∈ K, S.symm x ∈ K) (x : E) :
    K.starProjection (S x) = S (K.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h _ (K.starProjection_apply_mem x))
  intro w hw
  have hi := S.inner_map_map (x - K.starProjection x) (S.symm w)
  rw [S.apply_symm_apply, map_sub] at hi
  rw [hi]
  exact Submodule.starProjection_inner_eq_zero x _ (h' w hw)

section Sectorwise

variable {K : ℕ → Type*} [∀ n, NormedAddCommGroup (K n)] [∀ n, NormedSpace ℂ (K n)]

theorem sectorwise_memℓp (e : ∀ n, K n ≃ₗᵢ[ℂ] K n) (u : lp K 2) :
    Memℓp (fun n => e n (u n)) 2 :=
  (lp.memℓp u).norm.mono fun n => ((e n).norm_map (u n)).le

/-- Coordinatewise action of a family of linear maps on the square-summable sum. -/
def sectorwiseLinear (e : ∀ n, K n ≃ₗᵢ[ℂ] K n) : lp K 2 →ₗ[ℂ] lp K 2 where
  toFun u := ⟨fun n => e n (u n), sectorwise_memℓp e u⟩
  map_add' u v := by
    apply lp.ext
    funext n
    exact map_add (e n) (u n) (v n)
  map_smul' c u := by
    apply lp.ext
    funext n
    exact map_smul (e n) c (u n)

theorem sectorwiseLinear_norm (e : ∀ n, K n ≃ₗᵢ[ℂ] K n) (u : lp K 2) :
    ‖sectorwiseLinear e u‖ = ‖u‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h (n : ℕ) : ‖sectorwiseLinear e u n‖ = ‖u n‖ := (e n).norm_map (u n)
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  simp only [h]

/-- A family of unitaries acting sector by sector is a unitary of the direct sum. -/
def sectorwise (e : ∀ n, K n ≃ₗᵢ[ℂ] K n) : lp K 2 ≃ₗᵢ[ℂ] lp K 2 where
  toLinearMap := sectorwiseLinear e
  invFun := sectorwiseLinear fun n => (e n).symm
  left_inv u := by
    apply lp.ext
    funext n
    exact (e n).symm_apply_apply (u n)
  right_inv u := by
    apply lp.ext
    funext n
    exact (e n).apply_symm_apply (u n)
  norm_map' := sectorwiseLinear_norm e

@[simp] theorem sectorwise_apply (e : ∀ n, K n ≃ₗᵢ[ℂ] K n) (u : lp K 2) (n : ℕ) :
    sectorwise e u n = e n (u n) := rfl

@[simp] theorem sectorwise_symm_apply (e : ∀ n, K n ≃ₗᵢ[ℂ] K n) (u : lp K 2) (n : ℕ) :
    (sectorwise e).symm u n = (e n).symm (u n) := rfl

end Sectorwise

section OneParticle

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measure-preserving relabelling of the one-particle points together with a
measurable unimodular weight. It acts by `(U f)(p) = weight p * f (map p)`. -/
structure PointwiseUnitary (μ : Measure Ω) where
  map : Ω ≃ᵐ Ω
  preserving : MeasurePreserving map μ μ
  weight : Ω → ℂ
  measurable_weight : Measurable weight
  norm_weight : ∀ p, ‖weight p‖ = 1

namespace PointwiseUnitary

variable {μ : Measure Ω} (U : PointwiseUnitary μ)

theorem weight_ne_zero (p : Ω) : U.weight p ≠ 0 := by
  intro h
  have h1 := U.norm_weight p
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- The inverse relabelling with the compensating weight. -/
def symm : PointwiseUnitary μ where
  map := U.map.symm
  preserving := MeasurePreserving.symm U.map U.preserving
  weight p := (U.weight (U.map.symm p))⁻¹
  measurable_weight := (U.measurable_weight.comp U.map.symm.measurable).inv
  norm_weight p := by rw [norm_inv, U.norm_weight, inv_one]

@[simp] theorem symm_map_apply (p : Ω) : U.symm.map p = U.map.symm p := rfl

@[simp] theorem symm_weight (p : Ω) : U.symm.weight p = (U.weight (U.map.symm p))⁻¹ := rfl

/-- Every function invariant under the relabelling is invariant under its inverse. -/
theorem symm_invariant {β : Type*} (D : Ω → β) (hD : ∀ p, D (U.map p) = D p) (p : Ω) :
    D (U.symm.map p) = D p := by
  rw [← hD (U.symm.map p), symm_map_apply, MeasurableEquiv.apply_symm_apply]

theorem memLp (f : Lp ℂ 2 μ) : MemLp (fun p => U.weight p * f (U.map p)) 2 μ := by
  have hc : MemLp (f ∘ U.map) 2 μ := (Lp.memLp f).comp_measurePreserving U.preserving
  apply hc.of_le (U.measurable_weight.aestronglyMeasurable.mul hc.aestronglyMeasurable)
  exact ae_of_all _ fun p => by
    simp only [Pi.mul_apply, Function.comp_apply, norm_mul, U.norm_weight, one_mul, le_refl]

/-- The pointwise action as a linear map of L². -/
def toLinear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (U.memLp f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(U.memLp (f + g)).coeFn_toLp, (U.memLp f).coeFn_toLp,
      (U.memLp g).coeFn_toLp, U.preserving.quasiMeasurePreserving.ae (Lp.coeFn_add f g),
      Lp.coeFn_add ((U.memLp f).toLp _) ((U.memLp g).toLp _)] with p h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₅, Pi.add_apply, h₂, h₃, h₄, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(U.memLp (c • f)).coeFn_toLp, (U.memLp f).coeFn_toLp,
      U.preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul c f),
      Lp.coeFn_smul c ((U.memLp f).toLp _)] with p h₁ h₂ h₃ h₄
    rw [h₁, RingHom.id_apply, h₄, Pi.smul_apply, h₂, h₃, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring

theorem toLinear_ae (f : Lp ℂ 2 μ) :
    U.toLinear f =ᵐ[μ] fun p => U.weight p * f (U.map p) :=
  (U.memLp f).coeFn_toLp

theorem norm_toLinear (f : Lp ℂ 2 μ) : ‖U.toLinear f‖ = ‖f‖ := by
  have h1 : eLpNorm (fun p => U.weight p * f (U.map p)) 2 μ = eLpNorm (f ∘ U.map) 2 μ :=
    eLpNorm_congr_norm_ae (ae_of_all _ fun p => by
      simp only [Function.comp_apply, norm_mul, U.norm_weight, one_mul])
  change ‖(U.memLp f).toLp _‖ = ‖f‖
  rw [Lp.norm_toLp, h1, eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) U.preserving,
    Lp.norm_def]

theorem symm_toLinear_toLinear (f : Lp ℂ 2 μ) : U.symm.toLinear (U.toLinear f) = f := by
  apply Lp.ext
  filter_upwards [U.symm.toLinear_ae (U.toLinear f),
    U.symm.preserving.quasiMeasurePreserving.ae (U.toLinear_ae f)] with p h₁ h₂
  rw [h₁, h₂, symm_weight, symm_map_apply, MeasurableEquiv.apply_symm_apply,
    inv_mul_cancel_left₀ (U.weight_ne_zero _)]

theorem toLinear_symm_toLinear (f : Lp ℂ 2 μ) : U.toLinear (U.symm.toLinear f) = f := by
  apply Lp.ext
  filter_upwards [U.toLinear_ae (U.symm.toLinear f),
    U.preserving.quasiMeasurePreserving.ae (U.symm.toLinear_ae f)] with p h₁ h₂
  rw [h₁, h₂, symm_weight, symm_map_apply, MeasurableEquiv.symm_apply_apply,
    mul_inv_cancel_left₀ (U.weight_ne_zero _)]

end PointwiseUnitary

variable {μ : Measure Ω}

/-- The one-particle unitary `(U f)(p) = weight p * f (map p)`. -/
def oneParticle (U : PointwiseUnitary μ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearMap := U.toLinear
  invFun := U.symm.toLinear
  left_inv := U.symm_toLinear_toLinear
  right_inv := U.toLinear_symm_toLinear
  norm_map' := U.norm_toLinear

theorem oneParticle_ae (U : PointwiseUnitary μ) (f : Lp ℂ 2 μ) :
    oneParticle U f =ᵐ[μ] fun p => U.weight p * f (U.map p) :=
  U.toLinear_ae f

/-- The inverse of a pointwise unitary is the pointwise unitary of the inverse data. -/
theorem oneParticle_symm_apply (U : PointwiseUnitary μ) (f : Lp ℂ 2 μ) :
    (oneParticle U).symm f = oneParticle U.symm f := rfl

/-- A multiplier invariant under the relabelling commutes with the pointwise unitary. -/
theorem oneParticle_mul_ae (U : PointwiseUnitary μ) (a : Ω → ℂ) (ha : ∀ p, a (U.map p) = a p)
    {f g : Lp ℂ 2 μ} (h : ∀ᵐ p ∂μ, f p = a p * g p) :
    ∀ᵐ p ∂μ, oneParticle U f p = a p * oneParticle U g p := by
  filter_upwards [oneParticle_ae U f, oneParticle_ae U g,
    U.preserving.quasiMeasurePreserving.ae h] with p h₁ h₂ h₃
  rw [h₁, h₂, h₃, ha]
  ring

end OneParticle

section Sectors

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]

namespace PointwiseUnitary

variable (U : PointwiseUnitary μ)

/-- The n-fold product of a pointwise unitary, with the product weight. -/
def power (n : ℕ) : PointwiseUnitary (SectorMeasure μ n) where
  map := MeasurableEquiv.piCongrRight fun _ => U.map
  preserving := measurePreserving_pi (fun _ => μ) (fun _ => μ) (fun _ => U.preserving)
  weight k := ∏ i, U.weight (k i)
  measurable_weight :=
    Finset.measurable_prod _ fun i _ => U.measurable_weight.comp (measurable_pi_apply i)
  norm_weight k := by
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => U.norm_weight (k i)

@[simp] theorem power_map_apply (n : ℕ) (k : Fin n → Ω) (i : Fin n) :
    (U.power n).map k i = U.map (k i) := rfl

@[simp] theorem power_weight (n : ℕ) (k : Fin n → Ω) :
    (U.power n).weight k = ∏ i, U.weight (k i) := rfl

end PointwiseUnitary

variable (U : PointwiseUnitary μ)

/-- The product unitary on the full n-photon product space. -/
def sectorMap (n : ℕ) : FullSector μ n ≃ₗᵢ[ℂ] FullSector μ n := oneParticle (U.power n)

theorem sectorMap_ae (n : ℕ) (u : FullSector μ n) :
    sectorMap U n u =ᵐ[SectorMeasure μ n] fun k =>
      (∏ i, U.weight (k i)) * u (fun i => U.map (k i)) :=
  oneParticle_ae (U.power n) u

private theorem piCongrLeft_perm {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n → Ω) :
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π k = fun j => k (π.symm j) := by
  funext j
  obtain ⟨i, rfl⟩ := π.surjective j
  rw [MeasurableEquiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]

/-- The product unitary commutes with every coordinate permutation. -/
theorem sectorMap_permutation (n : ℕ) (π : Equiv.Perm (Fin n)) (u : FullSector μ n) :
    sectorMap U n (permutation μ n π u) = permutation μ n π (sectorMap U n u) := by
  have hσ := measurePreserving_piCongrLeft (fun _ : Fin n => μ) π
  have hperm : ∀ᵐ k ∂SectorMeasure μ n, permutation μ n π u (fun i => U.map (k i)) =
      u (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π (fun i => U.map (k i))) :=
    (U.power n).preserving.quasiMeasurePreserving.ae (permutation_ae μ n π u)
  have hmap : ∀ᵐ k ∂SectorMeasure μ n,
      sectorMap U n u (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π k) =
        (∏ i, U.weight (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π k i)) *
          u (fun i => U.map (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π k i)) :=
    hσ.quasiMeasurePreserving.ae (sectorMap_ae U n u)
  apply Lp.ext
  filter_upwards [sectorMap_ae U n (permutation μ n π u), hperm,
    permutation_ae μ n π (sectorMap U n u), hmap] with k h₁ h₂ h₃ h₄
  rw [h₁, h₃, Function.comp_apply, h₄, h₂]
  simp only [piCongrLeft_perm]
  congr 1
  exact (Equiv.prod_comp π.symm (fun i => U.weight (k i))).symm

theorem sectorMap_symm_permutation (n : ℕ) (π : Equiv.Perm (Fin n)) (u : FullSector μ n) :
    (sectorMap U n).symm (permutation μ n π u) = permutation μ n π ((sectorMap U n).symm u) := by
  apply (sectorMap U n).injective
  rw [LinearIsometryEquiv.apply_symm_apply, sectorMap_permutation,
    LinearIsometryEquiv.apply_symm_apply]

theorem sectorMap_mem {n : ℕ} {u : FullSector μ n} (hu : u ∈ symmetricSubspace μ n) :
    sectorMap U n u ∈ symmetricSubspace μ n := by
  intro π
  rw [← sectorMap_permutation, hu π]

theorem sectorMap_symm_mem {n : ℕ} {u : FullSector μ n} (hu : u ∈ symmetricSubspace μ n) :
    (sectorMap U n).symm u ∈ symmetricSubspace μ n := by
  intro π
  rw [← sectorMap_symm_permutation, hu π]

/-- The product unitary maps the symmetric sector onto itself. -/
theorem sectorMap_symmetricSubspace (n : ℕ) :
    (symmetricSubspace μ n).map (sectorMap U n).toLinearEquiv.toLinearMap =
      symmetricSubspace μ n := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact sectorMap_mem U hu
  · intro u hu
    exact ⟨(sectorMap U n).symm u, sectorMap_symm_mem U hu,
      (sectorMap U n).apply_symm_apply u⟩

/-- The product unitary commutes with the projection onto symmetric wave functions. -/
theorem sectorMap_starProjection (n : ℕ) (u : FullSector μ n) :
    (symmetricSubspace μ n).starProjection (sectorMap U n u) =
      sectorMap U n ((symmetricSubspace μ n).starProjection u) :=
  starProjection_unitary_commute (sectorMap U n) (symmetricSubspace μ n)
    (fun _ hx => sectorMap_mem U hx) (fun _ hx => sectorMap_symm_mem U hx) u

theorem sectorMap_symmetrizer (n : ℕ) (u : FullSector μ n) :
    symmetrizer μ n (sectorMap U n u) = sectorMap U n (symmetrizer μ n u) :=
  sectorMap_starProjection U n u

theorem PointwiseUnitary.ae_power {n : ℕ} {P : (Fin n → Ω) → Prop}
    (h : ∀ᵐ v ∂SectorMeasure μ n, P v) :
    ∀ᵐ k ∂SectorMeasure μ n, P (fun i => U.map (k i)) :=
  (U.power n).preserving.quasiMeasurePreserving.ae h

private theorem ae_head {n : ℕ} {P : Ω → Prop} (h : ∀ᵐ p ∂μ, P p) :
    ∀ᵐ k ∂SectorMeasure μ (n + 1), P (k 0) :=
  (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (n + 1) => μ) (i := 0)).eventually h

private theorem ae_tail {n : ℕ} {P : (Fin n → Ω) → Prop}
    (h : ∀ᵐ v ∂SectorMeasure μ n, P v) :
    ∀ᵐ k ∂SectorMeasure μ (n + 1), P (fun i : Fin n => k i.succ) := by
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
  have h2 : ∀ᵐ z ∂μ.prod (SectorMeasure μ n), P z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ)).ae h
  exact hp.quasiMeasurePreserving.ae h2

/-- The product unitary intertwines tensor insertion with the transformed kernel. -/
theorem sectorMap_tensorInsertion (n : ℕ) (f : Lp ℂ 2 μ) (u : FullSector μ n) :
    sectorMap U (n + 1) (tensorInsertion μ n f u) =
      tensorInsertion μ n (oneParticle U f) (sectorMap U n u) := by
  apply Lp.ext
  filter_upwards [sectorMap_ae U (n + 1) (tensorInsertion μ n f u),
    U.ae_power (tensorInsertion_ae μ n f u),
    tensorInsertion_ae μ n (oneParticle U f) (sectorMap U n u),
    ae_head (n := n) (oneParticle_ae U f), ae_tail (sectorMap_ae U n u)]
    with k h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂, h₃, h₄, h₅, Fin.prod_univ_succ]
  ring

/-- The unitary restricted to the symmetric n-photon sector. -/
def symSectorMap (n : ℕ) : Sector μ n ≃ₗᵢ[ℂ] Sector μ n :=
  restrictUnitary (sectorMap U n) (symmetricSubspace μ n) (fun _ hx => sectorMap_mem U hx)
    (fun _ hx => sectorMap_symm_mem U hx)

@[simp] theorem symSectorMap_val (n : ℕ) (u : Sector μ n) :
    (symSectorMap U n u).val = sectorMap U n u.val := rfl

@[simp] theorem symSectorMap_symm_val (n : ℕ) (u : Sector μ n) :
    ((symSectorMap U n).symm u).val = (sectorMap U n).symm u.val := rfl

theorem creationSector_val (n : ℕ) (f : Lp ℂ 2 μ) (u : Sector μ n) :
    (creationSector μ n f u).val = (Real.sqrt (n + 1 : ℝ) : ℂ) •
      (symmetricSubspace μ (n + 1)).starProjection (tensorInsertion μ n f u.val) := rfl

/-- Creation is covariant: the transformed kernel creates the transformed vector. -/
theorem symSectorMap_creationSector (n : ℕ) (f : Lp ℂ 2 μ) (u : Sector μ n) :
    symSectorMap U (n + 1) (creationSector μ n f u) =
      creationSector μ n (oneParticle U f) (symSectorMap U n u) := by
  apply Subtype.ext
  rw [symSectorMap_val, creationSector_val, creationSector_val, symSectorMap_val,
    LinearIsometryEquiv.map_smul, ← sectorMap_starProjection, sectorMap_tensorInsertion]

/-- Annihilation is covariant, by adjointness and unitarity. -/
theorem symSectorMap_annihilationSector (n : ℕ) (f : Lp ℂ 2 μ) (v : Sector μ (n + 1)) :
    symSectorMap U n (annihilationSector μ n f v) =
      annihilationSector μ n (oneParticle U f) (symSectorMap U (n + 1) v) := by
  apply ext_inner_left ℂ
  intro w
  obtain ⟨w, rfl⟩ := (symSectorMap U n).surjective w
  rw [← annihilationSector_duality, ← symSectorMap_creationSector,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map,
    annihilationSector_duality]

/-- The second quantization of a pointwise unitary, acting sector by sector. -/
def fockMap : Fock μ ≃ₗᵢ[ℂ] Fock μ := sectorwise fun n => symSectorMap U n

@[simp] theorem fockMap_apply (u : Fock μ) (n : ℕ) :
    fockMap U u n = symSectorMap U n (u n) := rfl

@[simp] theorem fockMap_symm_apply (u : Fock μ) (n : ℕ) :
    (fockMap U).symm u n = (symSectorMap U n).symm (u n) := rfl

/-- The Fock unitary commutes with the photon-number projections. -/
theorem fockMap_photonSector (n : ℕ) (u : Fock μ) :
    fockMap U (photonSector μ n u) = photonSector μ n (fockMap U u) := by
  apply lp.ext
  funext m
  by_cases h : m = n
  · subst h
    simp only [fockMap_apply, photonSector, sector_coordinate]
  · simp only [fockMap_apply, photonSector, sector_coordinate_ne _ n m h, map_zero]

end Sectors

section Photon

/-- Square-root dispersion is invariant under a length-preserving relabelling. -/
theorem power_sectorDispersion (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (n : ℕ) (k : Fin n → PhotonMode) :
    sectorDispersion n ((U.power n).map k) = sectorDispersion n k :=
  Finset.sum_congr rfl fun i _ => hU (k i)

theorem fockMap_graph (U : PointwiseUnitary photonMeasure) (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖)
    {u v : PhotonFock} (h : (u, v) ∈ radiationRoot.graph) :
    (fockMap U u, fockMap U v) ∈ radiationRoot.graph := by
  rw [radiationRoot_graph_iff] at h ⊢
  intro n
  exact oneParticle_mul_ae (U.power n) (fun k => (Real.sqrt (sectorDispersion n k) : ℂ))
    (fun k => congrArg (fun t : ℝ => (Real.sqrt t : ℂ)) (power_sectorDispersion U hU n k)) (h n)

theorem fockMap_symm_graph (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) {u v : PhotonFock} (h : (u, v) ∈ radiationRoot.graph) :
    ((fockMap U).symm u, (fockMap U).symm v) ∈ radiationRoot.graph := by
  rw [radiationRoot_graph_iff] at h ⊢
  intro n
  exact oneParticle_mul_ae (U.power n).symm (fun k => (Real.sqrt (sectorDispersion n k) : ℂ))
    (fun k => congrArg (fun t : ℝ => (Real.sqrt t : ℂ))
      ((U.power n).symm_invariant (sectorDispersion n) (power_sectorDispersion U hU n) k)) (h n)

theorem fockMap_domain (U : PointwiseUnitary photonMeasure) (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖)
    {u : PhotonFock} (hu : u ∈ radiationRoot.domain) : fockMap U u ∈ radiationRoot.domain :=
  LinearPMap.mem_domain_of_mem_graph (fockMap_graph U hU (radiationRoot.mem_graph ⟨u, hu⟩))

/-- On the square-root domain the Fock unitary commutes with the radiation root. -/
theorem radiationRoot_fockMap (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (u : radiationRoot.domain) :
    radiationRoot ⟨fockMap U u, fockMap_domain U hU u.property⟩ = fockMap U (radiationRoot u) :=
  radiationRoot.mem_graph_snd_inj (radiationRoot.mem_graph _)
    (fockMap_graph U hU (radiationRoot.mem_graph u)) rfl

/-- The Fock unitary restricted to the closed radiation graph. -/
def radiationGraphMap (U : PointwiseUnitary photonMeasure) (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) :
    RadiationGraphSpace ≃ₗᵢ[ℂ] RadiationGraphSpace :=
  restrictUnitary (prodUnitary (fockMap U)) radiationRoot.graph
    (fun x hx => by
      obtain ⟨u, v⟩ := x
      exact fockMap_graph U hU hx)
    (fun x hx => by
      obtain ⟨u, v⟩ := x
      exact fockMap_symm_graph U hU hx)

theorem radiationGraphInclusion_map (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (q : RadiationGraphSpace) :
    radiationGraphInclusion (radiationGraphMap U hU q) = fockMap U (radiationGraphInclusion q) :=
  rfl

theorem radiationGraphDerivative_map (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (q : RadiationGraphSpace) :
    radiationGraphDerivative (radiationGraphMap U hU q) =
      fockMap U (radiationGraphDerivative q) :=
  rfl

/-- A length-preserving pointwise unitary maps weighted kernels to weighted kernels. -/
def kernelMap (U : PointwiseUnitary photonMeasure) (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) :
    WeightedPhotonKernel ≃ₗᵢ[ℂ] WeightedPhotonKernel :=
  restrictUnitary (prodUnitary (oneParticle U)) weightedKernelSubspace
    (fun _ hx => oneParticle_mul_ae U (fun p => (Real.sqrt ‖p.1‖ : ℂ))
      (fun p => congrArg (fun t : ℝ => (Real.sqrt t : ℂ)) (hU p)) hx)
    (fun _ hx => oneParticle_mul_ae U.symm (fun p => (Real.sqrt ‖p.1‖ : ℂ))
      (fun p => congrArg (fun t : ℝ => (Real.sqrt t : ℂ))
        (U.symm_invariant (fun p => ‖p.1‖) hU p)) hx)

@[simp] theorem kernelMap_fst (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (k : WeightedPhotonKernel) :
    (kernelMap U hU k).val.1 = oneParticle U k.val.1 := rfl

@[simp] theorem kernelMap_snd (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (k : WeightedPhotonKernel) :
    (kernelMap U hU k).val.2 = oneParticle U k.val.2 := rfl

/-- Graph-domain annihilation is covariant under the pointwise unitary. -/
theorem kernelAnnihilation_map (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelAnnihilation (kernelMap U hU k) (radiationGraphMap U hU q) =
      fockMap U (kernelAnnihilation k q) := by
  apply lp.ext
  funext n
  change annihilationSector photonMeasure n (kernelMap U hU k).val.1
      (radiationGraphInclusion (radiationGraphMap U hU q) (n + 1)) =
    symSectorMap U n (annihilationSector photonMeasure n k.val.1
      (radiationGraphInclusion q (n + 1)))
  rw [kernelMap_fst, radiationGraphInclusion_map, fockMap_apply,
    symSectorMap_annihilationSector]

/-- Graph-domain creation is covariant under the pointwise unitary. -/
theorem kernelCreation_map (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelCreation C (kernelMap U hU k) (radiationGraphMap U hU q) =
      fockMap U (kernelCreation C k q) := by
  apply lp.ext
  funext n
  cases n with
  | zero => exact (map_zero (symSectorMap U 0)).symm
  | succ n =>
    change creationSector photonMeasure n (kernelMap U hU k).val.1
        (radiationGraphInclusion (radiationGraphMap U hU q) n) =
      symSectorMap U (n + 1) (creationSector photonMeasure n k.val.1
        (radiationGraphInclusion q n))
    rw [kernelMap_fst, radiationGraphInclusion_map, fockMap_apply,
      symSectorMap_creationSector]

/-- The Segal field is covariant under the pointwise unitary. -/
theorem kernelField_map (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelField C (kernelMap U hU k) (radiationGraphMap U hU q) =
      fockMap U (kernelField C k q) := by
  simp only [kernelField, add_apply, kernelAnnihilation_map, kernelCreation_map,
    LinearIsometryEquiv.map_add]

end Photon

/-! ### Antiunitary pointwise maps

Complex conjugation of wave functions is a conjugate-linear isometric
involution. It commutes with permutations, symmetric projection and tensor
insertion, so creation and annihilation transform with the conjugated
kernel. Composing it with a pointwise unitary gives the general pointwise
antiunitary `(J f)(p) = weight p * conj (f (map p))`.
-/

section AntiRestriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A conjugate-linear isometric bijection preserving a subspace in both
directions restricts to the subspace. -/
def restrictAntiunitary (S : E ≃ₗᵢ⋆[ℂ] E) (K : Submodule ℂ E) (h : ∀ x ∈ K, S x ∈ K)
    (h' : ∀ x ∈ K, S.symm x ∈ K) : K ≃ₗᵢ⋆[ℂ] K where
  toFun x := ⟨S x, h x x.2⟩
  invFun x := ⟨S.symm x, h' x x.2⟩
  map_add' x y := Subtype.ext (map_add S (x : E) (y : E))
  map_smul' c x := Subtype.ext (S.map_smulₛₗ c (x : E))
  left_inv x := Subtype.ext (S.symm_apply_apply x)
  right_inv x := Subtype.ext (S.apply_symm_apply x)
  norm_map' x := S.norm_map x

@[simp] theorem restrictAntiunitary_val (S : E ≃ₗᵢ⋆[ℂ] E) (K : Submodule ℂ E)
    (h : ∀ x ∈ K, S x ∈ K) (h' : ∀ x ∈ K, S.symm x ∈ K) (x : K) :
    (restrictAntiunitary S K h h' x).val = S x.val := rfl

/-- The same conjugate-linear isometry acting on both components of a pair. -/
def prodAntiunitary (S : E ≃ₗᵢ⋆[ℂ] E) : (E × E) ≃ₗᵢ⋆[ℂ] (E × E) where
  toFun x := (S x.1, S x.2)
  invFun x := (S.symm x.1, S.symm x.2)
  map_add' x y := Prod.ext (map_add S x.1 y.1) (map_add S x.2 y.2)
  map_smul' c x := Prod.ext (S.map_smulₛₗ c x.1) (S.map_smulₛₗ c x.2)
  left_inv x := Prod.ext (S.symm_apply_apply x.1) (S.symm_apply_apply x.2)
  right_inv x := Prod.ext (S.apply_symm_apply x.1) (S.apply_symm_apply x.2)
  norm_map' x := by
    change max ‖S x.1‖ ‖S x.2‖ = max ‖x.1‖ ‖x.2‖
    rw [S.norm_map, S.norm_map]

end AntiRestriction

/-- A conjugate-linear isometry conjugates inner products, by polarization. -/
theorem inner_antiunitary {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (J : E ≃ₗᵢ⋆[ℂ] E) (x y : E) : ⟪J x, J y⟫_ℂ = (starRingEnd ℂ) ⟪x, y⟫_ℂ := by
  have h1 : J x + J y = J (x + y) := (map_add J x y).symm
  have h2 : J x - J y = J (x - y) := (map_sub J x y).symm
  have h3 : J x - (RCLike.I : ℂ) • J y = J (x + (RCLike.I : ℂ) • y) := by
    rw [map_add, J.map_smulₛₗ, RCLike.conj_I, neg_smul, sub_eq_add_neg]
  have h4 : J x + (RCLike.I : ℂ) • J y = J (x - (RCLike.I : ℂ) • y) := by
    rw [map_sub, J.map_smulₛₗ, RCLike.conj_I, neg_smul, sub_neg_eq_add]
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (J x) (J y),
    inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) x y, h1, h2, h3, h4, J.norm_map, J.norm_map,
    J.norm_map, J.norm_map]
  simp only [map_div₀, map_mul, map_sub, map_add, map_pow, RCLike.conj_ofReal, RCLike.conj_I,
    map_ofNat]
  ring

/-- A conjugate-linear isometry preserving a closed subspace in both directions
commutes with the orthogonal projection onto it. -/
theorem starProjection_antiunitary_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : E ≃ₗᵢ⋆[ℂ] E) (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (h : ∀ x ∈ K, S x ∈ K) (h' : ∀ x ∈ K, S.symm x ∈ K) (x : E) :
    K.starProjection (S x) = S (K.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h _ (K.starProjection_apply_mem x))
  intro w hw
  have hi := inner_antiunitary S (x - K.starProjection x) (S.symm w)
  rw [S.apply_symm_apply, map_sub] at hi
  rw [hi, Submodule.starProjection_inner_eq_zero x _ (h' w hw), map_zero]

section AntiSectorwise

variable {K : ℕ → Type*} [∀ n, NormedAddCommGroup (K n)] [∀ n, NormedSpace ℂ (K n)]

theorem antiSectorwise_memℓp (e : ∀ n, K n ≃ₗᵢ⋆[ℂ] K n) (u : lp K 2) :
    Memℓp (fun n => e n (u n)) 2 :=
  (lp.memℓp u).norm.mono fun n => ((e n).norm_map (u n)).le

/-- Coordinatewise action of a family of conjugate-linear maps. -/
def antiSectorwiseLinear (e : ∀ n, K n ≃ₗᵢ⋆[ℂ] K n) : lp K 2 →ₛₗ[starRingEnd ℂ] lp K 2 where
  toFun u := ⟨fun n => e n (u n), antiSectorwise_memℓp e u⟩
  map_add' u v := by
    apply lp.ext
    funext n
    exact map_add (e n) (u n) (v n)
  map_smul' c u := by
    apply lp.ext
    funext n
    exact (e n).map_smulₛₗ c (u n)

theorem antiSectorwiseLinear_norm (e : ∀ n, K n ≃ₗᵢ⋆[ℂ] K n) (u : lp K 2) :
    ‖antiSectorwiseLinear e u‖ = ‖u‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h (n : ℕ) : ‖antiSectorwiseLinear e u n‖ = ‖u n‖ := (e n).norm_map (u n)
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  simp only [h]

/-- A family of conjugate-linear isometric bijections acting sector by sector. -/
def antiSectorwise (e : ∀ n, K n ≃ₗᵢ⋆[ℂ] K n) : lp K 2 ≃ₗᵢ⋆[ℂ] lp K 2 where
  toLinearMap := antiSectorwiseLinear e
  invFun := antiSectorwiseLinear fun n => (e n).symm
  left_inv u := by
    apply lp.ext
    funext n
    exact (e n).symm_apply_apply (u n)
  right_inv u := by
    apply lp.ext
    funext n
    exact (e n).apply_symm_apply (u n)
  norm_map' := antiSectorwiseLinear_norm e

@[simp] theorem antiSectorwise_apply (e : ∀ n, K n ≃ₗᵢ⋆[ℂ] K n) (u : lp K 2) (n : ℕ) :
    antiSectorwise e u n = e n (u n) := rfl

end AntiSectorwise

section Conjugation

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

theorem conj_memLp (f : Lp ℂ 2 ν) : MemLp (fun p => (starRingEnd ℂ) (f p)) 2 ν :=
  (Lp.memLp f).of_le
    (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
    (ae_of_all _ fun p => (Complex.norm_conj (f p)).le)

/-- Pointwise complex conjugation as a conjugate-linear map of L². -/
def conjLinear : Lp ℂ 2 ν →ₛₗ[starRingEnd ℂ] Lp ℂ 2 ν where
  toFun f := (conj_memLp f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(conj_memLp (f + g)).coeFn_toLp, (conj_memLp f).coeFn_toLp,
      (conj_memLp g).coeFn_toLp, Lp.coeFn_add f g,
      Lp.coeFn_add ((conj_memLp f).toLp _) ((conj_memLp g).toLp _)] with p h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₅, Pi.add_apply, h₂, h₃, h₄, Pi.add_apply, map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(conj_memLp (c • f)).coeFn_toLp, (conj_memLp f).coeFn_toLp,
      Lp.coeFn_smul c f, Lp.coeFn_smul ((starRingEnd ℂ) c) ((conj_memLp f).toLp _)]
      with p h₁ h₂ h₃ h₄
    rw [h₁, h₄, Pi.smul_apply, h₂, h₃, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]

theorem conjLinear_ae (f : Lp ℂ 2 ν) :
    conjLinear f =ᵐ[ν] fun p => (starRingEnd ℂ) (f p) :=
  (conj_memLp f).coeFn_toLp

theorem conjLinear_conjLinear (f : Lp ℂ 2 ν) : conjLinear (conjLinear f) = f := by
  apply Lp.ext
  filter_upwards [conjLinear_ae (conjLinear f), conjLinear_ae f] with p h₁ h₂
  rw [h₁, h₂, Complex.conj_conj]

theorem norm_conjLinear (f : Lp ℂ 2 ν) : ‖conjLinear f‖ = ‖f‖ := by
  have h1 : eLpNorm (fun p => (starRingEnd ℂ) (f p)) 2 ν = eLpNorm f 2 ν :=
    eLpNorm_congr_norm_ae (ae_of_all _ fun p => Complex.norm_conj (f p))
  change ‖(conj_memLp f).toLp _‖ = ‖f‖
  rw [Lp.norm_toLp, h1, Lp.norm_def]

/-- Complex conjugation of wave functions, a conjugate-linear isometric involution. -/
def conjL2 : Lp ℂ 2 ν ≃ₗᵢ⋆[ℂ] Lp ℂ 2 ν where
  toLinearMap := conjLinear
  invFun := conjLinear
  left_inv := conjLinear_conjLinear
  right_inv := conjLinear_conjLinear
  norm_map' := norm_conjLinear

theorem conjL2_ae (f : Lp ℂ 2 ν) : conjL2 f =ᵐ[ν] fun p => (starRingEnd ℂ) (f p) :=
  conjLinear_ae f

theorem conjL2_symm_apply (f : Lp ℂ 2 ν) : (conjL2 (ν := ν)).symm f = conjL2 f := rfl

/-- Conjugation commutes with multiplication by a real-valued function. -/
theorem conjL2_mul_ae (a : X → ℂ) (ha : ∀ p, (starRingEnd ℂ) (a p) = a p) {f g : Lp ℂ 2 ν}
    (h : ∀ᵐ p ∂ν, f p = a p * g p) : ∀ᵐ p ∂ν, conjL2 f p = a p * conjL2 g p := by
  filter_upwards [conjL2_ae f, conjL2_ae g, h] with p h₁ h₂ h₃
  rw [h₁, h₂, h₃, map_mul, ha]

end Conjugation

section ConjSectors

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

/-- Complex conjugation on the full n-photon product space. -/
def sectorConj (n : ℕ) : FullSector μ n ≃ₗᵢ⋆[ℂ] FullSector μ n := conjL2

omit [SigmaFinite μ] in
theorem sectorConj_ae (n : ℕ) (u : FullSector μ n) :
    sectorConj μ n u =ᵐ[SectorMeasure μ n] fun k => (starRingEnd ℂ) (u k) :=
  conjL2_ae u

omit [SigmaFinite μ] in
theorem sectorConj_symm_apply (n : ℕ) (u : FullSector μ n) :
    (sectorConj μ n).symm u = sectorConj μ n u := rfl

theorem sectorConj_permutation (n : ℕ) (π : Equiv.Perm (Fin n)) (u : FullSector μ n) :
    sectorConj μ n (permutation μ n π u) = permutation μ n π (sectorConj μ n u) := by
  have hσ := measurePreserving_piCongrLeft (fun _ : Fin n => μ) π
  apply Lp.ext
  filter_upwards [sectorConj_ae μ n (permutation μ n π u), permutation_ae μ n π u,
    permutation_ae μ n π (sectorConj μ n u),
    hσ.quasiMeasurePreserving.ae (sectorConj_ae μ n u)] with k h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃]
  simp only [Function.comp_apply]
  rw [h₄]

theorem sectorConj_mem {n : ℕ} {u : FullSector μ n} (hu : u ∈ symmetricSubspace μ n) :
    sectorConj μ n u ∈ symmetricSubspace μ n := by
  intro π
  rw [← sectorConj_permutation, hu π]

theorem sectorConj_symm_mem {n : ℕ} {u : FullSector μ n} (hu : u ∈ symmetricSubspace μ n) :
    (sectorConj μ n).symm u ∈ symmetricSubspace μ n := by
  rw [sectorConj_symm_apply]
  exact sectorConj_mem μ hu

theorem sectorConj_starProjection (n : ℕ) (u : FullSector μ n) :
    (symmetricSubspace μ n).starProjection (sectorConj μ n u) =
      sectorConj μ n ((symmetricSubspace μ n).starProjection u) :=
  starProjection_antiunitary_commute (sectorConj μ n) (symmetricSubspace μ n)
    (fun _ hx => sectorConj_mem μ hx) (fun _ hx => sectorConj_symm_mem μ hx) u

/-- Conjugation intertwines tensor insertion with the conjugated kernel. -/
theorem sectorConj_tensorInsertion (n : ℕ) (f : Lp ℂ 2 μ) (u : FullSector μ n) :
    sectorConj μ (n + 1) (tensorInsertion μ n f u) =
      tensorInsertion μ n (conjL2 f) (sectorConj μ n u) := by
  apply Lp.ext
  filter_upwards [sectorConj_ae μ (n + 1) (tensorInsertion μ n f u), tensorInsertion_ae μ n f u,
    tensorInsertion_ae μ n (conjL2 f) (sectorConj μ n u),
    ae_head (n := n) (conjL2_ae f), ae_tail (sectorConj_ae μ n u)] with k h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂, h₃, h₄, h₅, map_mul]

/-- Conjugation restricted to the symmetric n-photon sector. -/
def symConj (n : ℕ) : Sector μ n ≃ₗᵢ⋆[ℂ] Sector μ n :=
  restrictAntiunitary (sectorConj μ n) (symmetricSubspace μ n) (fun _ hx => sectorConj_mem μ hx)
    (fun _ hx => sectorConj_symm_mem μ hx)

@[simp] theorem symConj_val (n : ℕ) (u : Sector μ n) :
    (symConj μ n u).val = sectorConj μ n u.val := rfl

/-- Creation transforms with the conjugated kernel; the real prefactor is unchanged. -/
theorem symConj_creationSector (n : ℕ) (f : Lp ℂ 2 μ) (u : Sector μ n) :
    symConj μ (n + 1) (creationSector μ n f u) =
      creationSector μ n (conjL2 f) (symConj μ n u) := by
  apply Subtype.ext
  rw [symConj_val, creationSector_val, creationSector_val, symConj_val,
    LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal, ← sectorConj_starProjection,
    sectorConj_tensorInsertion]

/-- Annihilation transforms with the conjugated kernel. -/
theorem symConj_annihilationSector (n : ℕ) (f : Lp ℂ 2 μ) (v : Sector μ (n + 1)) :
    symConj μ n (annihilationSector μ n f v) =
      annihilationSector μ n (conjL2 f) (symConj μ (n + 1) v) := by
  apply ext_inner_left ℂ
  intro w
  obtain ⟨w, rfl⟩ := (symConj μ n).surjective w
  rw [← annihilationSector_duality, ← symConj_creationSector, inner_antiunitary,
    inner_antiunitary, annihilationSector_duality]

/-- Complex conjugation on the bosonic Fock space, sector by sector. -/
def fockConj : Fock μ ≃ₗᵢ⋆[ℂ] Fock μ := antiSectorwise fun n => symConj μ n

@[simp] theorem fockConj_apply (u : Fock μ) (n : ℕ) :
    fockConj μ u n = symConj μ n (u n) := rfl

end ConjSectors

section AntiSectors

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]

/-- The pointwise antiunitary `(J f)(p) = weight p * conj (f (map p))`. -/
def antiParticle (U : PointwiseUnitary μ) : Lp ℂ 2 μ ≃ₗᵢ⋆[ℂ] Lp ℂ 2 μ :=
  conjL2.trans (oneParticle U)

omit [SigmaFinite μ] in
theorem antiParticle_apply (U : PointwiseUnitary μ) (f : Lp ℂ 2 μ) :
    antiParticle U f = oneParticle U (conjL2 f) := rfl

omit [SigmaFinite μ] in
theorem antiParticle_ae (U : PointwiseUnitary μ) (f : Lp ℂ 2 μ) :
    antiParticle U f =ᵐ[μ] fun p => U.weight p * (starRingEnd ℂ) (f (U.map p)) := by
  rw [antiParticle_apply]
  filter_upwards [oneParticle_ae U (conjL2 f),
    U.preserving.quasiMeasurePreserving.ae (conjL2_ae f)] with p h₁ h₂
  rw [h₁, h₂]

/-- The antiunitary on the symmetric n-photon sector. -/
def antiSymSectorMap (U : PointwiseUnitary μ) (n : ℕ) : Sector μ n ≃ₗᵢ⋆[ℂ] Sector μ n :=
  (symConj μ n).trans (symSectorMap U n)

theorem antiSymSectorMap_apply (U : PointwiseUnitary μ) (n : ℕ) (u : Sector μ n) :
    antiSymSectorMap U n u = symSectorMap U n (symConj μ n u) := rfl

/-- Creation is covariant under the antiunitary. -/
theorem antiSymSectorMap_creationSector (U : PointwiseUnitary μ) (n : ℕ) (f : Lp ℂ 2 μ)
    (u : Sector μ n) :
    antiSymSectorMap U (n + 1) (creationSector μ n f u) =
      creationSector μ n (antiParticle U f) (antiSymSectorMap U n u) := by
  rw [antiSymSectorMap_apply, antiSymSectorMap_apply, antiParticle_apply,
    symConj_creationSector, symSectorMap_creationSector]

/-- Annihilation is covariant under the antiunitary. -/
theorem antiSymSectorMap_annihilationSector (U : PointwiseUnitary μ) (n : ℕ) (f : Lp ℂ 2 μ)
    (v : Sector μ (n + 1)) :
    antiSymSectorMap U n (annihilationSector μ n f v) =
      annihilationSector μ n (antiParticle U f) (antiSymSectorMap U (n + 1) v) := by
  rw [antiSymSectorMap_apply, antiSymSectorMap_apply, antiParticle_apply,
    symConj_annihilationSector, symSectorMap_annihilationSector]

/-- The second quantization of the pointwise antiunitary. -/
def fockAnti (U : PointwiseUnitary μ) : Fock μ ≃ₗᵢ⋆[ℂ] Fock μ :=
  (fockConj μ).trans (fockMap U)

@[simp] theorem fockAnti_apply (U : PointwiseUnitary μ) (u : Fock μ) (n : ℕ) :
    fockAnti U u n = antiSymSectorMap U n (u n) := rfl

end AntiSectors

section AntiPhoton

theorem fockConj_graph {u v : PhotonFock} (h : (u, v) ∈ radiationRoot.graph) :
    (fockConj photonMeasure u, fockConj photonMeasure v) ∈ radiationRoot.graph := by
  rw [radiationRoot_graph_iff] at h ⊢
  intro n
  exact conjL2_mul_ae (fun k => (Real.sqrt (sectorDispersion n k) : ℂ))
    (fun k => Complex.conj_ofReal _) (h n)

theorem fockConj_symm_graph {u v : PhotonFock} (h : (u, v) ∈ radiationRoot.graph) :
    ((fockConj photonMeasure).symm u, (fockConj photonMeasure).symm v) ∈
      radiationRoot.graph := by
  rw [radiationRoot_graph_iff] at h ⊢
  intro n
  exact conjL2_mul_ae (fun k => (Real.sqrt (sectorDispersion n k) : ℂ))
    (fun k => Complex.conj_ofReal _) (h n)

/-- Conjugation restricted to the closed radiation graph. -/
def radiationGraphConj : RadiationGraphSpace ≃ₗᵢ⋆[ℂ] RadiationGraphSpace :=
  restrictAntiunitary (prodAntiunitary (fockConj photonMeasure)) radiationRoot.graph
    (fun x hx => by
      obtain ⟨u, v⟩ := x
      exact fockConj_graph hx)
    (fun x hx => by
      obtain ⟨u, v⟩ := x
      exact fockConj_symm_graph hx)

theorem radiationGraphInclusion_conj (q : RadiationGraphSpace) :
    radiationGraphInclusion (radiationGraphConj q) =
      fockConj photonMeasure (radiationGraphInclusion q) := rfl

theorem radiationGraphDerivative_conj (q : RadiationGraphSpace) :
    radiationGraphDerivative (radiationGraphConj q) =
      fockConj photonMeasure (radiationGraphDerivative q) := rfl

/-- Conjugation maps weighted kernels to weighted kernels. -/
def kernelConj : WeightedPhotonKernel ≃ₗᵢ⋆[ℂ] WeightedPhotonKernel :=
  restrictAntiunitary (prodAntiunitary conjL2) weightedKernelSubspace
    (fun _ hx => conjL2_mul_ae (ν := photonMeasure)
      (fun p : PhotonMode => (Real.sqrt ‖p.1‖ : ℂ)) (fun _ => Complex.conj_ofReal _) hx)
    (fun _ hx => conjL2_mul_ae (ν := photonMeasure)
      (fun p : PhotonMode => (Real.sqrt ‖p.1‖ : ℂ)) (fun _ => Complex.conj_ofReal _) hx)

@[simp] theorem kernelConj_fst (k : WeightedPhotonKernel) :
    (kernelConj k).val.1 = conjL2 k.val.1 := rfl

theorem kernelAnnihilation_conj (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelAnnihilation (kernelConj k) (radiationGraphConj q) =
      fockConj photonMeasure (kernelAnnihilation k q) := by
  apply lp.ext
  funext n
  change annihilationSector photonMeasure n (kernelConj k).val.1
      (radiationGraphInclusion (radiationGraphConj q) (n + 1)) =
    symConj photonMeasure n (annihilationSector photonMeasure n k.val.1
      (radiationGraphInclusion q (n + 1)))
  rw [kernelConj_fst, radiationGraphInclusion_conj, fockConj_apply,
    symConj_annihilationSector]

theorem kernelCreation_conj (C : CanonicalSectorCCR photonMeasure) (k : WeightedPhotonKernel)
    (q : RadiationGraphSpace) :
    kernelCreation C (kernelConj k) (radiationGraphConj q) =
      fockConj photonMeasure (kernelCreation C k q) := by
  apply lp.ext
  funext n
  cases n with
  | zero => exact (map_zero (symConj photonMeasure 0)).symm
  | succ n =>
    change creationSector photonMeasure n (kernelConj k).val.1
        (radiationGraphInclusion (radiationGraphConj q) n) =
      symConj photonMeasure (n + 1) (creationSector photonMeasure n k.val.1
        (radiationGraphInclusion q n))
    rw [kernelConj_fst, radiationGraphInclusion_conj, fockConj_apply, symConj_creationSector]

theorem kernelField_conj (C : CanonicalSectorCCR photonMeasure) (k : WeightedPhotonKernel)
    (q : RadiationGraphSpace) :
    kernelField C (kernelConj k) (radiationGraphConj q) =
      fockConj photonMeasure (kernelField C k q) := by
  simp only [kernelField, add_apply, kernelAnnihilation_conj, kernelCreation_conj,
    LinearIsometryEquiv.map_add]

/-- The pointwise antiunitary restricted to the radiation graph. -/
def radiationGraphAnti (U : PointwiseUnitary photonMeasure) (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) :
    RadiationGraphSpace ≃ₗᵢ⋆[ℂ] RadiationGraphSpace :=
  radiationGraphConj.trans (radiationGraphMap U hU)

/-- The pointwise antiunitary on weighted kernels. -/
def kernelAnti (U : PointwiseUnitary photonMeasure) (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) :
    WeightedPhotonKernel ≃ₗᵢ⋆[ℂ] WeightedPhotonKernel :=
  kernelConj.trans (kernelMap U hU)

theorem kernelAnti_fst (U : PointwiseUnitary photonMeasure) (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖)
    (k : WeightedPhotonKernel) : (kernelAnti U hU k).val.1 = antiParticle U k.val.1 := rfl

theorem radiationGraphInclusion_anti (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (q : RadiationGraphSpace) :
    radiationGraphInclusion (radiationGraphAnti U hU q) = fockAnti U (radiationGraphInclusion q) :=
  rfl

theorem radiationGraphDerivative_anti (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (q : RadiationGraphSpace) :
    radiationGraphDerivative (radiationGraphAnti U hU q) =
      fockAnti U (radiationGraphDerivative q) :=
  rfl

theorem kernelAnnihilation_anti (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelAnnihilation (kernelAnti U hU k) (radiationGraphAnti U hU q) =
      fockAnti U (kernelAnnihilation k q) := by
  change kernelAnnihilation (kernelMap U hU (kernelConj k))
      (radiationGraphMap U hU (radiationGraphConj q)) =
    fockMap U (fockConj photonMeasure (kernelAnnihilation k q))
  rw [kernelAnnihilation_map, kernelAnnihilation_conj]

theorem kernelCreation_anti (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelCreation C (kernelAnti U hU k) (radiationGraphAnti U hU q) =
      fockAnti U (kernelCreation C k q) := by
  change kernelCreation C (kernelMap U hU (kernelConj k))
      (radiationGraphMap U hU (radiationGraphConj q)) =
    fockMap U (fockConj photonMeasure (kernelCreation C k q))
  rw [kernelCreation_map, kernelCreation_conj]

theorem kernelField_anti (U : PointwiseUnitary photonMeasure)
    (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖) (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelField C (kernelAnti U hU k) (radiationGraphAnti U hU q) =
      fockAnti U (kernelField C k q) := by
  change kernelField C (kernelMap U hU (kernelConj k))
      (radiationGraphMap U hU (radiationGraphConj q)) =
    fockMap U (fockConj photonMeasure (kernelField C k q))
  rw [kernelField_map, kernelField_conj]

end AntiPhoton

end GptLean.TransformationsFock
