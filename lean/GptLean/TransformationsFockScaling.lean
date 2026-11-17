import GptLean.TransformationsFockPointwise
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

/-!
Scaled pointwise one-photon unitaries and the photon dilation.

A measurable bijection `φ` of the one-photon space which multiplies the
measure by a constant, `φ_* μ = c μ`, together with a measurable weight of
constant modulus `c ^ (-1/2)`, acts unitarily on L² by
`(U f)(p) = m p * f (φ p)`. On the n-fold product the weight is the product
weight and the measure is multiplied by `c ^ n`. As for measure-preserving
relabellings, the product unitary commutes with coordinate permutations,
symmetric projection and tensor insertion, so creation and annihilation are
covariant and the sectorwise action is a Fock unitary. If `φ` multiplies
momentum lengths by `s > 0`, the square-root radiation operator is multiplied
by `s ^ (-1/2)`, so the Fock unitary acts on the radiation graph by
`(u, v) ↦ (Γ u, s ^ (-1/2) • Γ v)`. The photon dilation
`(Υ_λ f)(k, pol) = λ ^ (3/2) * f (λ k, pol)` is the case `c = λ ^ (-3)`,
`s = λ`.
-/

noncomputable section

namespace GptLean.TransformationsFock

open MeasureTheory Filter
open GptLean.PhysicalFock
open scoped ENNReal InnerProductSpace

section OneParticle

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable bijection which multiplies the measure by the constant `scale`,
together with a measurable weight of modulus `scale ^ (-1/2)`. It acts by
`(U f)(p) = weight p * f (map p)`. -/
structure ScaledPointwiseUnitary (μ : Measure Ω) where
  map : Ω ≃ᵐ Ω
  scale : ℝ
  scale_pos : 0 < scale
  map_measure : Measure.map map μ = ENNReal.ofReal scale • μ
  weight : Ω → ℂ
  measurable_weight : Measurable weight
  norm_weight_sq : ∀ p, ‖weight p‖ ^ 2 * scale = 1

namespace ScaledPointwiseUnitary

variable {μ : Measure Ω} (U : ScaledPointwiseUnitary μ)

theorem quasiMeasurePreserving : Measure.QuasiMeasurePreserving U.map μ μ := by
  refine ⟨U.map.measurable, ?_⟩
  rw [U.map_measure]
  exact Measure.smul_absolutelyContinuous

theorem norm_weight_sq' (p : Ω) : ‖U.weight p‖ ^ 2 = U.scale⁻¹ :=
  eq_inv_of_mul_eq_one_left (U.norm_weight_sq p)

theorem norm_weight (p : Ω) : ‖U.weight p‖ = (Real.sqrt U.scale)⁻¹ := by
  have h2 : (‖U.weight p‖ * Real.sqrt U.scale) ^ 2 = 1 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt U.scale_pos.le, U.norm_weight_sq, one_pow]
  have h3 : ‖U.weight p‖ * Real.sqrt U.scale = 1 :=
    (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) zero_le_one).mp h2
  exact eq_inv_of_mul_eq_one_left h3

theorem weight_ne_zero (p : Ω) : U.weight p ≠ 0 := by
  intro h
  have h1 := U.norm_weight_sq p
  rw [h, norm_zero] at h1
  norm_num at h1

/-- The inverse map multiplies the measure by the inverse constant. -/
theorem symm_map_measure :
    Measure.map U.map.symm μ = ENNReal.ofReal U.scale⁻¹ • μ := by
  have hc := U.scale_pos
  have h0 : ENNReal.ofReal U.scale ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have h1 : μ = ENNReal.ofReal U.scale • Measure.map U.map.symm μ := by
    have h := congrArg (Measure.map U.map.symm) U.map_measure
    rw [MeasurableEquiv.map_symm_map, Measure.map_smul] at h
    exact h
  have h2 : Measure.map U.map.symm μ = (ENNReal.ofReal U.scale)⁻¹ •
      (ENNReal.ofReal U.scale • Measure.map U.map.symm μ) := by
    rw [smul_smul, ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_smul]
  rw [ENNReal.ofReal_inv_of_pos hc, h2, ← h1]

/-- The inverse relabelling with the compensating weight. -/
def symm : ScaledPointwiseUnitary μ where
  map := U.map.symm
  scale := U.scale⁻¹
  scale_pos := inv_pos.mpr U.scale_pos
  map_measure := U.symm_map_measure
  weight p := (U.weight (U.map.symm p))⁻¹
  measurable_weight := (U.measurable_weight.comp U.map.symm.measurable).inv
  norm_weight_sq p := by
    rw [norm_inv, inv_pow, ← mul_inv, U.norm_weight_sq, inv_one]

@[simp] theorem symm_map_apply (p : Ω) : U.symm.map p = U.map.symm p := rfl

@[simp] theorem symm_weight (p : Ω) : U.symm.weight p = (U.weight (U.map.symm p))⁻¹ := rfl

@[simp] theorem symm_scale : U.symm.scale = U.scale⁻¹ := rfl

/-- A function multiplied by `s` under the map is multiplied by `s⁻¹` under the inverse. -/
theorem symm_scaled_invariant (D : Ω → ℝ) {s : ℝ} (hs : s ≠ 0)
    (hD : ∀ p, D (U.map p) = s * D p) (p : Ω) : D (U.symm.map p) = s⁻¹ * D p := by
  have h := hD (U.symm.map p)
  rw [symm_map_apply, MeasurableEquiv.apply_symm_apply] at h
  rw [symm_map_apply, h, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

theorem memLp_comp (f : Lp ℂ 2 μ) : MemLp (f ∘ U.map) 2 μ := by
  have h : MemLp f 2 (Measure.map U.map μ) := by
    rw [U.map_measure]
    exact (Lp.memLp f).smul_measure ENNReal.ofReal_ne_top
  exact h.comp_of_map U.map.measurable.aemeasurable

theorem memLp (f : Lp ℂ 2 μ) : MemLp (fun p => U.weight p * f (U.map p)) 2 μ := by
  have hc := U.memLp_comp f
  apply hc.of_le_mul (c := (Real.sqrt U.scale)⁻¹)
    (U.measurable_weight.aestronglyMeasurable.mul hc.aestronglyMeasurable)
  exact ae_of_all _ fun p => le_of_eq (by rw [Pi.mul_apply, norm_mul, U.norm_weight])

/-- The scaled pointwise action as a linear map of L². -/
def toLinear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (U.memLp f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(U.memLp (f + g)).coeFn_toLp, (U.memLp f).coeFn_toLp,
      (U.memLp g).coeFn_toLp, U.quasiMeasurePreserving.ae (Lp.coeFn_add f g),
      Lp.coeFn_add ((U.memLp f).toLp _) ((U.memLp g).toLp _)] with p h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₅, Pi.add_apply, h₂, h₃, h₄, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(U.memLp (c • f)).coeFn_toLp, (U.memLp f).coeFn_toLp,
      U.quasiMeasurePreserving.ae (Lp.coeFn_smul c f),
      Lp.coeFn_smul c ((U.memLp f).toLp _)] with p h₁ h₂ h₃ h₄
    rw [h₁, RingHom.id_apply, h₄, Pi.smul_apply, h₂, h₃, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring

theorem toLinear_ae (f : Lp ℂ 2 μ) :
    U.toLinear f =ᵐ[μ] fun p => U.weight p * f (U.map p) :=
  (U.memLp f).coeFn_toLp

/-- Change of variables: the weight exactly compensates the scaling of the measure. -/
theorem norm_toLinear (f : Lp ℂ 2 μ) : ‖U.toLinear f‖ = ‖f‖ := by
  have hc := U.scale_pos
  have h2 : ∫ p, ‖U.toLinear f p‖ ^ 2 ∂μ = ∫ p, U.scale⁻¹ * ‖f (U.map p)‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [U.toLinear_ae f] with p hp
    rw [hp, norm_mul, mul_pow, U.norm_weight_sq']
  have h3 : ∫ p, ‖f (U.map p)‖ ^ 2 ∂μ = U.scale * ∫ p, ‖f p‖ ^ 2 ∂μ := by
    have e1 := U.map.measurableEmbedding.integral_map (μ := μ) (fun y => ‖f y‖ ^ 2)
    rw [U.map_measure, integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul] at e1
    exact e1.symm
  have h1 : ‖U.toLinear f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [PhotonKernelLocalization.l2_norm_sq_eq_integral (U.toLinear f),
      PhotonKernelLocalization.l2_norm_sq_eq_integral f, h2, integral_const_mul, h3,
      ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

theorem symm_toLinear_toLinear (f : Lp ℂ 2 μ) : U.symm.toLinear (U.toLinear f) = f := by
  apply Lp.ext
  filter_upwards [U.symm.toLinear_ae (U.toLinear f),
    U.symm.quasiMeasurePreserving.ae (U.toLinear_ae f)] with p h₁ h₂
  rw [h₁, h₂, symm_weight, symm_map_apply, MeasurableEquiv.apply_symm_apply,
    inv_mul_cancel_left₀ (U.weight_ne_zero _)]

theorem toLinear_symm_toLinear (f : Lp ℂ 2 μ) : U.toLinear (U.symm.toLinear f) = f := by
  apply Lp.ext
  filter_upwards [U.toLinear_ae (U.symm.toLinear f),
    U.quasiMeasurePreserving.ae (U.symm.toLinear_ae f)] with p h₁ h₂
  rw [h₁, h₂, symm_weight, symm_map_apply, MeasurableEquiv.symm_apply_apply,
    mul_inv_cancel_left₀ (U.weight_ne_zero _)]

end ScaledPointwiseUnitary

variable {μ : Measure Ω}

/-- The one-particle unitary `(U f)(p) = weight p * f (map p)` of a scaled relabelling. -/
def oneParticleScaled (U : ScaledPointwiseUnitary μ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearMap := U.toLinear
  invFun := U.symm.toLinear
  left_inv := U.symm_toLinear_toLinear
  right_inv := U.toLinear_symm_toLinear
  norm_map' := U.norm_toLinear

theorem oneParticleScaled_ae (U : ScaledPointwiseUnitary μ) (f : Lp ℂ 2 μ) :
    oneParticleScaled U f =ᵐ[μ] fun p => U.weight p * f (U.map p) :=
  U.toLinear_ae f

/-- The inverse is the scaled pointwise unitary of the inverse data. -/
theorem oneParticleScaled_symm_apply (U : ScaledPointwiseUnitary μ) (f : Lp ℂ 2 μ) :
    (oneParticleScaled U).symm f = oneParticleScaled U.symm f := rfl

end OneParticle

section Sectors

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]

namespace ScaledPointwiseUnitary

variable (U : ScaledPointwiseUnitary μ)

/-- The coordinatewise map multiplies the product measure by `scale ^ n`. -/
theorem power_map_measure (n : ℕ) :
    Measure.map (MeasurableEquiv.piCongrRight fun _ : Fin n => U.map) (SectorMeasure μ n) =
      ENNReal.ofReal (U.scale ^ n) • SectorMeasure μ n := by
  have hc := U.scale_pos
  have hpow : ENNReal.ofReal (U.scale ^ n) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hc n)).ne'
  have hbox : ∀ s : Fin n → Set Ω, (∀ i, MeasurableSet (s i)) →
      Measure.map (MeasurableEquiv.piCongrRight fun _ : Fin n => U.map) (SectorMeasure μ n)
        (Set.pi Set.univ s) = ENNReal.ofReal (U.scale ^ n) * ∏ i, μ (s i) := by
    intro s hs
    have hpre : (MeasurableEquiv.piCongrRight fun _ : Fin n => U.map) ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ fun i => U.map ⁻¹' s i := Set.ext fun _ => Iff.rfl
    have hi : ∀ i, μ (U.map ⁻¹' s i) = ENNReal.ofReal U.scale * μ (s i) := fun i => by
      rw [← Measure.map_apply U.map.measurable (hs i), U.map_measure, Measure.smul_apply,
        smul_eq_mul]
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs), hpre,
      Measure.pi_pi]
    simp only [hi]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.ofReal_pow hc.le]
  have h1 : SectorMeasure μ n = (ENNReal.ofReal (U.scale ^ n))⁻¹ •
      Measure.map (MeasurableEquiv.piCongrRight fun _ : Fin n => U.map) (SectorMeasure μ n) := by
    apply Measure.pi_eq
    intro s hs
    rw [Measure.smul_apply, hbox s hs, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hpow ENNReal.ofReal_ne_top, one_mul]
  calc Measure.map (MeasurableEquiv.piCongrRight fun _ : Fin n => U.map) (SectorMeasure μ n)
      = (ENNReal.ofReal (U.scale ^ n) * (ENNReal.ofReal (U.scale ^ n))⁻¹) •
          Measure.map (MeasurableEquiv.piCongrRight fun _ : Fin n => U.map)
            (SectorMeasure μ n) := by
        rw [ENNReal.mul_inv_cancel hpow ENNReal.ofReal_ne_top, one_smul]
    _ = ENNReal.ofReal (U.scale ^ n) • SectorMeasure μ n := by
        rw [← smul_smul, ← h1]

/-- The n-fold product of a scaled pointwise unitary, with the product weight. -/
def power (n : ℕ) : ScaledPointwiseUnitary (SectorMeasure μ n) where
  map := MeasurableEquiv.piCongrRight fun _ => U.map
  scale := U.scale ^ n
  scale_pos := pow_pos U.scale_pos n
  map_measure := U.power_map_measure n
  weight k := ∏ i, U.weight (k i)
  measurable_weight :=
    Finset.measurable_prod _ fun i _ => U.measurable_weight.comp (measurable_pi_apply i)
  norm_weight_sq k := by
    rw [norm_prod, ← Finset.prod_pow, ← Fin.prod_const n U.scale, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => U.norm_weight_sq (k i)

@[simp] theorem power_map_apply (n : ℕ) (k : Fin n → Ω) (i : Fin n) :
    (U.power n).map k i = U.map (k i) := rfl

@[simp] theorem power_weight (n : ℕ) (k : Fin n → Ω) :
    (U.power n).weight k = ∏ i, U.weight (k i) := rfl

theorem ae_power {n : ℕ} {P : (Fin n → Ω) → Prop} (h : ∀ᵐ v ∂SectorMeasure μ n, P v) :
    ∀ᵐ k ∂SectorMeasure μ n, P (fun i => U.map (k i)) :=
  (U.power n).quasiMeasurePreserving.ae h

end ScaledPointwiseUnitary

private theorem scaled_ae_head {n : ℕ} {P : Ω → Prop} (h : ∀ᵐ p ∂μ, P p) :
    ∀ᵐ k ∂SectorMeasure μ (n + 1), P (k 0) :=
  (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (n + 1) => μ) (i := 0)).eventually h

private theorem scaled_ae_tail {n : ℕ} {P : (Fin n → Ω) → Prop}
    (h : ∀ᵐ v ∂SectorMeasure μ n, P v) :
    ∀ᵐ k ∂SectorMeasure μ (n + 1), P (fun i : Fin n => k i.succ) := by
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
  have h2 : ∀ᵐ z ∂μ.prod (SectorMeasure μ n), P z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ)).ae h
  exact hp.quasiMeasurePreserving.ae h2

omit [SigmaFinite μ] in
private theorem perm_piCongrLeft {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n → Ω) :
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π k = fun j => k (π.symm j) := by
  funext j
  obtain ⟨i, rfl⟩ := π.surjective j
  rw [MeasurableEquiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]

variable (U : ScaledPointwiseUnitary μ)

/-- The product unitary on the full n-photon product space. -/
def sectorScaled (n : ℕ) : FullSector μ n ≃ₗᵢ[ℂ] FullSector μ n := oneParticleScaled (U.power n)

theorem sectorScaled_ae (n : ℕ) (u : FullSector μ n) :
    sectorScaled U n u =ᵐ[SectorMeasure μ n] fun k =>
      (∏ i, U.weight (k i)) * u (fun i => U.map (k i)) :=
  oneParticleScaled_ae (U.power n) u

/-- The product unitary commutes with every coordinate permutation. -/
theorem sectorScaled_permutation (n : ℕ) (π : Equiv.Perm (Fin n)) (u : FullSector μ n) :
    sectorScaled U n (permutation μ n π u) = permutation μ n π (sectorScaled U n u) := by
  have hσ := measurePreserving_piCongrLeft (fun _ : Fin n => μ) π
  have hperm : ∀ᵐ k ∂SectorMeasure μ n, permutation μ n π u (fun i => U.map (k i)) =
      u (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π (fun i => U.map (k i))) :=
    U.ae_power (permutation_ae μ n π u)
  have hmap : ∀ᵐ k ∂SectorMeasure μ n,
      sectorScaled U n u (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π k) =
        (∏ i, U.weight (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π k i)) *
          u (fun i => U.map (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π k i)) :=
    hσ.quasiMeasurePreserving.ae (sectorScaled_ae U n u)
  apply Lp.ext
  filter_upwards [sectorScaled_ae U n (permutation μ n π u), hperm,
    permutation_ae μ n π (sectorScaled U n u), hmap] with k h₁ h₂ h₃ h₄
  rw [h₁, h₃, Function.comp_apply, h₄, h₂]
  simp only [perm_piCongrLeft]
  congr 1
  exact (Equiv.prod_comp π.symm (fun i => U.weight (k i))).symm

theorem sectorScaled_symm_permutation (n : ℕ) (π : Equiv.Perm (Fin n)) (u : FullSector μ n) :
    (sectorScaled U n).symm (permutation μ n π u) =
      permutation μ n π ((sectorScaled U n).symm u) := by
  apply (sectorScaled U n).injective
  rw [LinearIsometryEquiv.apply_symm_apply, sectorScaled_permutation,
    LinearIsometryEquiv.apply_symm_apply]

theorem sectorScaled_mem {n : ℕ} {u : FullSector μ n} (hu : u ∈ symmetricSubspace μ n) :
    sectorScaled U n u ∈ symmetricSubspace μ n := by
  intro π
  rw [← sectorScaled_permutation, hu π]

theorem sectorScaled_symm_mem {n : ℕ} {u : FullSector μ n} (hu : u ∈ symmetricSubspace μ n) :
    (sectorScaled U n).symm u ∈ symmetricSubspace μ n := by
  intro π
  rw [← sectorScaled_symm_permutation, hu π]

/-- The product unitary commutes with the projection onto symmetric wave functions. -/
theorem sectorScaled_starProjection (n : ℕ) (u : FullSector μ n) :
    (symmetricSubspace μ n).starProjection (sectorScaled U n u) =
      sectorScaled U n ((symmetricSubspace μ n).starProjection u) :=
  starProjection_unitary_commute (sectorScaled U n) (symmetricSubspace μ n)
    (fun _ hx => sectorScaled_mem U hx) (fun _ hx => sectorScaled_symm_mem U hx) u

theorem sectorScaled_symmetrizer (n : ℕ) (u : FullSector μ n) :
    symmetrizer μ n (sectorScaled U n u) = sectorScaled U n (symmetrizer μ n u) :=
  sectorScaled_starProjection U n u

/-- The product unitary intertwines tensor insertion with the transformed kernel. -/
theorem sectorScaled_tensorInsertion (n : ℕ) (f : Lp ℂ 2 μ) (u : FullSector μ n) :
    sectorScaled U (n + 1) (tensorInsertion μ n f u) =
      tensorInsertion μ n (oneParticleScaled U f) (sectorScaled U n u) := by
  apply Lp.ext
  filter_upwards [sectorScaled_ae U (n + 1) (tensorInsertion μ n f u),
    U.ae_power (tensorInsertion_ae μ n f u),
    tensorInsertion_ae μ n (oneParticleScaled U f) (sectorScaled U n u),
    scaled_ae_head (n := n) (oneParticleScaled_ae U f), scaled_ae_tail (sectorScaled_ae U n u)]
    with k h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂, h₃, h₄, h₅, Fin.prod_univ_succ]
  ring

/-- The unitary restricted to the symmetric n-photon sector. -/
def symSectorScaled (n : ℕ) : Sector μ n ≃ₗᵢ[ℂ] Sector μ n :=
  restrictUnitary (sectorScaled U n) (symmetricSubspace μ n) (fun _ hx => sectorScaled_mem U hx)
    (fun _ hx => sectorScaled_symm_mem U hx)

@[simp] theorem symSectorScaled_val (n : ℕ) (u : Sector μ n) :
    (symSectorScaled U n u).val = sectorScaled U n u.val := rfl

@[simp] theorem symSectorScaled_symm_val (n : ℕ) (u : Sector μ n) :
    ((symSectorScaled U n).symm u).val = (sectorScaled U n).symm u.val := rfl

/-- Creation is covariant: the transformed kernel creates the transformed vector. -/
theorem symSectorScaled_creationSector (n : ℕ) (f : Lp ℂ 2 μ) (u : Sector μ n) :
    symSectorScaled U (n + 1) (creationSector μ n f u) =
      creationSector μ n (oneParticleScaled U f) (symSectorScaled U n u) := by
  apply Subtype.ext
  rw [symSectorScaled_val, creationSector_val, creationSector_val, symSectorScaled_val,
    LinearIsometryEquiv.map_smul, ← sectorScaled_starProjection, sectorScaled_tensorInsertion]

/-- Annihilation is covariant, by adjointness and unitarity. -/
theorem symSectorScaled_annihilationSector (n : ℕ) (f : Lp ℂ 2 μ) (v : Sector μ (n + 1)) :
    symSectorScaled U n (annihilationSector μ n f v) =
      annihilationSector μ n (oneParticleScaled U f) (symSectorScaled U (n + 1) v) := by
  apply ext_inner_left ℂ
  intro w
  obtain ⟨w, rfl⟩ := (symSectorScaled U n).surjective w
  rw [← annihilationSector_duality, ← symSectorScaled_creationSector,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map,
    annihilationSector_duality]

/-- The second quantization of a scaled pointwise unitary, acting sector by sector. -/
def fockScaled : Fock μ ≃ₗᵢ[ℂ] Fock μ := sectorwise fun n => symSectorScaled U n

@[simp] theorem fockScaled_apply (u : Fock μ) (n : ℕ) :
    fockScaled U u n = symSectorScaled U n (u n) := rfl

@[simp] theorem fockScaled_symm_apply (u : Fock μ) (n : ℕ) :
    (fockScaled U).symm u n = (symSectorScaled U n).symm (u n) := rfl

/-- The Fock unitary commutes with the photon-number projections. -/
theorem fockScaled_photonSector (n : ℕ) (u : Fock μ) :
    fockScaled U (photonSector μ n u) = photonSector μ n (fockScaled U u) := by
  apply lp.ext
  funext m
  by_cases h : m = n
  · subst h
    simp only [fockScaled_apply, photonSector, sector_coordinate]
  · simp only [fockScaled_apply, photonSector, sector_coordinate_ne _ n m h, map_zero]

end Sectors

section ContinuousRestriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous linear equivalence preserving a subspace in both directions
restricts to the subspace. -/
def restrictCLE (S : E ≃L[ℂ] E) (K : Submodule ℂ E) (h : ∀ x ∈ K, S x ∈ K)
    (h' : ∀ x ∈ K, S.symm x ∈ K) : K ≃L[ℂ] K where
  toFun x := ⟨S x, h x x.2⟩
  invFun x := ⟨S.symm x, h' x x.2⟩
  map_add' x y := Subtype.ext (map_add S (x : E) (y : E))
  map_smul' c x := Subtype.ext (map_smul S c (x : E))
  left_inv x := Subtype.ext (S.symm_apply_apply x)
  right_inv x := Subtype.ext (S.apply_symm_apply x)
  continuous_toFun := (S.continuous.comp continuous_subtype_val).subtype_mk fun x => h _ x.2
  continuous_invFun :=
    (S.symm.continuous.comp continuous_subtype_val).subtype_mk fun x => h' _ x.2

@[simp] theorem restrictCLE_val (S : E ≃L[ℂ] E) (K : Submodule ℂ E)
    (h : ∀ x ∈ K, S x ∈ K) (h' : ∀ x ∈ K, S.symm x ∈ K) (x : K) :
    (restrictCLE S K h h' x).val = S x.val := rfl

@[simp] theorem restrictCLE_symm_val (S : E ≃L[ℂ] E) (K : Submodule ℂ E)
    (h : ∀ x ∈ K, S x ∈ K) (h' : ∀ x ∈ K, S.symm x ∈ K) (x : K) :
    ((restrictCLE S K h h').symm x).val = S.symm x.val := rfl

/-- A unitary on the first component and the same unitary times `t` on the second. -/
def prodScaled (S : E ≃ₗᵢ[ℂ] E) (t t' : ℂ) (h : t * t' = 1) (h' : t' * t = 1) :
    (E × E) ≃L[ℂ] (E × E) where
  toFun x := (S x.1, t • S x.2)
  invFun x := (S.symm x.1, t' • S.symm x.2)
  map_add' x y := Prod.ext (map_add S x.1 y.1) (by
    change t • S (x.2 + y.2) = t • S x.2 + t • S y.2
    rw [map_add, smul_add])
  map_smul' c x := Prod.ext (map_smul S c x.1) (by
    change t • S (c • x.2) = c • (t • S x.2)
    rw [map_smul, smul_comm])
  left_inv x := Prod.ext (S.symm_apply_apply x.1) (by
    change t' • S.symm (t • S x.2) = x.2
    rw [map_smul, S.symm_apply_apply, smul_smul, h', one_smul])
  right_inv x := Prod.ext (S.apply_symm_apply x.1) (by
    change t • S (t' • S.symm x.2) = x.2
    rw [map_smul, S.apply_symm_apply, smul_smul, h, one_smul])
  continuous_toFun := (S.continuous.comp continuous_fst).prodMk
    ((S.continuous.comp continuous_snd).const_smul t)
  continuous_invFun := (S.symm.continuous.comp continuous_fst).prodMk
    ((S.symm.continuous.comp continuous_snd).const_smul t')

@[simp] theorem prodScaled_apply (S : E ≃ₗᵢ[ℂ] E) (t t' : ℂ) (h : t * t' = 1)
    (h' : t' * t = 1) (x : E × E) : prodScaled S t t' h h' x = (S x.1, t • S x.2) := rfl

@[simp] theorem prodScaled_symm_apply (S : E ≃ₗᵢ[ℂ] E) (t t' : ℂ) (h : t * t' = 1)
    (h' : t' * t = 1) (x : E × E) :
    (prodScaled S t t' h h').symm x = (S.symm x.1, t' • S.symm x.2) := rfl

end ContinuousRestriction

section Photon

private theorem sqrt_ofReal_ne_zero {s : ℝ} (hs : 0 < s) : (Real.sqrt s : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne'

/-- If momentum lengths are multiplied by `s`, so is the sector dispersion. -/
theorem scaledPower_sectorDispersion (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ}
    (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) (n : ℕ) (k : Fin n → PhotonMode) :
    sectorDispersion n ((U.power n).map k) = s * sectorDispersion n k := by
  unfold sectorDispersion
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hU (k i)

/-- The square-root multiplier is rescaled by `√s` under the scaled unitary. -/
theorem oneParticleScaled_root_ae {n : ℕ}
    (V : ScaledPointwiseUnitary (SectorMeasure photonMeasure n)) {s : ℝ} (hs : 0 ≤ s)
    (hV : ∀ k, sectorDispersion n (V.map k) = s * sectorDispersion n k)
    {t : ℂ} (ht : t * (Real.sqrt s : ℂ) = 1) {u v : FullSector photonMeasure n}
    (h : ∀ᵐ k ∂SectorMeasure photonMeasure n,
      v k = (Real.sqrt (sectorDispersion n k) : ℂ) * u k) :
    ∀ᵐ k ∂SectorMeasure photonMeasure n, (t • oneParticleScaled V v) k =
      (Real.sqrt (sectorDispersion n k) : ℂ) * oneParticleScaled V u k := by
  filter_upwards [Lp.coeFn_smul t (oneParticleScaled V v), oneParticleScaled_ae V v,
    oneParticleScaled_ae V u, V.quasiMeasurePreserving.ae h] with k h₁ h₂ h₃ h₄
  rw [h₁, Pi.smul_apply, smul_eq_mul, h₂, h₃, h₄, hV, Real.sqrt_mul hs, Complex.ofReal_mul]
  linear_combination ((Real.sqrt (sectorDispersion n k) : ℂ) * V.weight k * u (V.map k)) * ht

/-- The Fock unitary maps graph pairs `(u, v)` to `(Γ u, s ^ (-1/2) • Γ v)`. -/
theorem fockScaled_graph (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ} (hs : 0 < s)
    (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) {u v : PhotonFock}
    (h : (u, v) ∈ radiationRoot.graph) :
    (fockScaled U u, (Real.sqrt s : ℂ)⁻¹ • fockScaled U v) ∈ radiationRoot.graph := by
  rw [radiationRoot_graph_iff] at h ⊢
  intro n
  exact oneParticleScaled_root_ae (U.power n) hs.le (scaledPower_sectorDispersion U hU n)
    (inv_mul_cancel₀ (sqrt_ofReal_ne_zero hs)) (h n)

/-- The inverse Fock unitary maps graph pairs `(u, v)` to `(Γ⁻¹ u, s ^ (1/2) • Γ⁻¹ v)`. -/
theorem fockScaled_symm_graph (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ} (hs : 0 < s)
    (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) {u v : PhotonFock}
    (h : (u, v) ∈ radiationRoot.graph) :
    ((fockScaled U).symm u, (Real.sqrt s : ℂ) • (fockScaled U).symm v) ∈
      radiationRoot.graph := by
  have hsq : (Real.sqrt s : ℂ) * (Real.sqrt s⁻¹ : ℂ) = 1 := by
    rw [Real.sqrt_inv, Complex.ofReal_inv, mul_inv_cancel₀ (sqrt_ofReal_ne_zero hs)]
  rw [radiationRoot_graph_iff] at h ⊢
  intro n
  exact oneParticleScaled_root_ae (U.power n).symm (inv_nonneg.mpr hs.le)
    ((U.power n).symm_scaled_invariant (sectorDispersion n) hs.ne'
      (scaledPower_sectorDispersion U hU n)) hsq (h n)

theorem fockScaled_domain (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ} (hs : 0 < s)
    (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) {u : PhotonFock} (hu : u ∈ radiationRoot.domain) :
    fockScaled U u ∈ radiationRoot.domain :=
  LinearPMap.mem_domain_of_mem_graph (fockScaled_graph U hs hU (radiationRoot.mem_graph ⟨u, hu⟩))

/-- On the square-root domain, `√H_f Γ = s ^ (-1/2) Γ √H_f`. -/
theorem radiationRoot_fockScaled (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ}
    (hs : 0 < s) (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) (u : radiationRoot.domain) :
    radiationRoot ⟨fockScaled U u, fockScaled_domain U hs hU u.property⟩ =
      (Real.sqrt s : ℂ)⁻¹ • fockScaled U (radiationRoot u) :=
  radiationRoot.mem_graph_snd_inj (radiationRoot.mem_graph _)
    (fockScaled_graph U hs hU (radiationRoot.mem_graph u)) rfl

/-- The induced map of the closed radiation graph. It is continuous but not
isometric for the graph norm. -/
def radiationScaled (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ} (hs : 0 < s)
    (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) : RadiationGraphSpace ≃L[ℂ] RadiationGraphSpace :=
  restrictCLE (prodScaled (fockScaled U) (Real.sqrt s : ℂ)⁻¹ (Real.sqrt s : ℂ)
      (inv_mul_cancel₀ (sqrt_ofReal_ne_zero hs)) (mul_inv_cancel₀ (sqrt_ofReal_ne_zero hs)))
    radiationRoot.graph
    (fun x hx => by
      obtain ⟨u, v⟩ := x
      exact fockScaled_graph U hs hU hx)
    (fun x hx => by
      obtain ⟨u, v⟩ := x
      exact fockScaled_symm_graph U hs hU hx)

theorem radiationGraphInclusion_scaled (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ}
    (hs : 0 < s) (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) (q : RadiationGraphSpace) :
    radiationGraphInclusion (radiationScaled U hs hU q) =
      fockScaled U (radiationGraphInclusion q) := rfl

theorem radiationGraphDerivative_scaled (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ}
    (hs : 0 < s) (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) (q : RadiationGraphSpace) :
    radiationGraphDerivative (radiationScaled U hs hU q) =
      (Real.sqrt s : ℂ)⁻¹ • fockScaled U (radiationGraphDerivative q) := rfl

/-- If `f = √ω g`, then `U f = √ω (√s U g)`. -/
theorem oneParticleScaled_kernel_ae (V : ScaledPointwiseUnitary photonMeasure) {s : ℝ}
    (hs : 0 ≤ s) (hV : ∀ p, ‖(V.map p).1‖ = s * ‖p.1‖) {t : ℂ} (ht : (Real.sqrt s : ℂ) = t)
    {f g : Lp ℂ 2 photonMeasure} (h : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p) :
    ∀ᵐ p ∂photonMeasure,
      oneParticleScaled V f p = (Real.sqrt ‖p.1‖ : ℂ) * (t • oneParticleScaled V g) p := by
  filter_upwards [oneParticleScaled_ae V f, oneParticleScaled_ae V g,
    Lp.coeFn_smul t (oneParticleScaled V g), V.quasiMeasurePreserving.ae h] with p h₁ h₂ h₃ h₄
  rw [h₁, h₃, Pi.smul_apply, smul_eq_mul, h₂, h₄, hV, Real.sqrt_mul hs, Complex.ofReal_mul, ← ht]
  ring

/-- The induced map of weighted kernels, `(f, g) ↦ (U f, √s • U g)`. -/
def kernelScaled (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ} (hs : 0 < s)
    (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) : WeightedPhotonKernel ≃L[ℂ] WeightedPhotonKernel :=
  restrictCLE (prodScaled (oneParticleScaled U) (Real.sqrt s : ℂ) (Real.sqrt s : ℂ)⁻¹
      (mul_inv_cancel₀ (sqrt_ofReal_ne_zero hs)) (inv_mul_cancel₀ (sqrt_ofReal_ne_zero hs)))
    weightedKernelSubspace
    (fun _ hx => oneParticleScaled_kernel_ae U hs.le hU rfl hx)
    (fun _ hx => oneParticleScaled_kernel_ae U.symm (inv_nonneg.mpr hs.le)
      (U.symm_scaled_invariant (fun p => ‖p.1‖) hs.ne' hU)
      (by rw [Real.sqrt_inv, Complex.ofReal_inv]) hx)

@[simp] theorem kernelScaled_fst (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ}
    (hs : 0 < s) (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) (k : WeightedPhotonKernel) :
    (kernelScaled U hs hU k).val.1 = oneParticleScaled U k.val.1 := rfl

@[simp] theorem kernelScaled_snd (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ}
    (hs : 0 < s) (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) (k : WeightedPhotonKernel) :
    (kernelScaled U hs hU k).val.2 = (Real.sqrt s : ℂ) • oneParticleScaled U k.val.2 := rfl

/-- Graph-domain annihilation is covariant under the scaled unitary. -/
theorem kernelAnnihilation_scaled (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ}
    (hs : 0 < s) (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) (k : WeightedPhotonKernel)
    (q : RadiationGraphSpace) :
    kernelAnnihilation (kernelScaled U hs hU k) (radiationScaled U hs hU q) =
      fockScaled U (kernelAnnihilation k q) := by
  apply lp.ext
  funext n
  change annihilationSector photonMeasure n (oneParticleScaled U k.val.1)
      (symSectorScaled U (n + 1) (radiationGraphInclusion q (n + 1))) =
    symSectorScaled U n (annihilationSector photonMeasure n k.val.1
      (radiationGraphInclusion q (n + 1)))
  exact (symSectorScaled_annihilationSector U n k.val.1 _).symm

/-- Graph-domain creation is covariant under the scaled unitary. -/
theorem kernelCreation_scaled (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ}
    (hs : 0 < s) (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelCreation C (kernelScaled U hs hU k) (radiationScaled U hs hU q) =
      fockScaled U (kernelCreation C k q) := by
  apply lp.ext
  funext n
  cases n with
  | zero => exact (map_zero (symSectorScaled U 0)).symm
  | succ n =>
    change creationSector photonMeasure n (oneParticleScaled U k.val.1)
        (symSectorScaled U n (radiationGraphInclusion q n)) =
      symSectorScaled U (n + 1) (creationSector photonMeasure n k.val.1
        (radiationGraphInclusion q n))
    exact (symSectorScaled_creationSector U n k.val.1 _).symm

/-- The Segal field is covariant under the scaled unitary. -/
theorem kernelField_scaled (U : ScaledPointwiseUnitary photonMeasure) {s : ℝ}
    (hs : 0 < s) (hU : ∀ p, ‖(U.map p).1‖ = s * ‖p.1‖) (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelField C (kernelScaled U hs hU k) (radiationScaled U hs hU q) =
      fockScaled U (kernelField C k q) := by
  simp only [kernelField, add_apply, kernelAnnihilation_scaled, kernelCreation_scaled,
    LinearIsometryEquiv.map_add]

end Photon

section Dilation

/-- Multiplication of the photon momentum by `lam`, with the polarization unchanged. -/
def momentumDilation (lam : ℝ) (hlam : 0 < lam) : PhotonMode ≃ᵐ PhotonMode :=
  (MeasurableEquiv.smul₀ lam hlam.ne').prodCongr (MeasurableEquiv.refl (Fin 2))

theorem momentumDilation_apply (lam : ℝ) (hlam : 0 < lam) (p : PhotonMode) :
    momentumDilation lam hlam p = (lam • p.1, p.2) := rfl

/-- Dilation by `lam` multiplies the photon measure by `lam ^ (-3)`. -/
theorem momentumDilation_map_measure (lam : ℝ) (hlam : 0 < lam) :
    Measure.map (momentumDilation lam hlam) photonMeasure =
      ENNReal.ofReal (lam ^ 3)⁻¹ • photonMeasure := by
  have h1 : Measure.map (fun k : Gaussian.FieldSpace => lam • k) volume =
      ENNReal.ofReal (lam ^ 3)⁻¹ • volume := by
    rw [Measure.map_addHaar_smul volume hlam.ne', finrank_euclideanSpace_fin,
      abs_of_pos (inv_pos.mpr (pow_pos hlam 3))]
  have h2 : (momentumDilation lam hlam : PhotonMode → PhotonMode) =
      Prod.map (fun k : Gaussian.FieldSpace => lam • k) id := rfl
  unfold photonMeasure
  rw [h2, ← Measure.map_prod_map volume Measure.count (measurable_const_smul lam) measurable_id,
    h1, Measure.map_id, Measure.prod_smul_left]

theorem rpow_three_halves_sq {lam : ℝ} (hlam : 0 < lam) : (lam ^ (3 / 2 : ℝ)) ^ 2 = lam ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le, ← Real.rpow_natCast lam 3]
  congr 1
  norm_num

/-- The data of the photon dilation `(Υ_λ f)(k, pol) = λ ^ (3/2) * f (λ k, pol)`. -/
def photonDilationData (lam : ℝ) (hlam : 0 < lam) : ScaledPointwiseUnitary photonMeasure where
  map := momentumDilation lam hlam
  scale := (lam ^ 3)⁻¹
  scale_pos := inv_pos.mpr (pow_pos hlam 3)
  map_measure := momentumDilation_map_measure lam hlam
  weight _ := ((lam ^ (3 / 2 : ℝ) : ℝ) : ℂ)
  measurable_weight := measurable_const
  norm_weight_sq _ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hlam _),
      rpow_three_halves_sq hlam, mul_inv_cancel₀ (pow_pos hlam 3).ne']

/-- The photon dilation, a unitary of the one-photon space. -/
def photonDilation (lam : ℝ) (hlam : 0 < lam) :
    Lp ℂ 2 photonMeasure ≃ₗᵢ[ℂ] Lp ℂ 2 photonMeasure :=
  oneParticleScaled (photonDilationData lam hlam)

theorem photonDilation_ae (lam : ℝ) (hlam : 0 < lam) (f : Lp ℂ 2 photonMeasure) :
    photonDilation lam hlam f =ᵐ[photonMeasure] fun p =>
      ((lam ^ (3 / 2 : ℝ) : ℝ) : ℂ) * f (lam • p.1, p.2) :=
  oneParticleScaled_ae (photonDilationData lam hlam) f

/-- Dilation multiplies momentum lengths by `lam`. -/
theorem photonDilation_momentum (lam : ℝ) (hlam : 0 < lam) (p : PhotonMode) :
    ‖((photonDilationData lam hlam).map p).1‖ = lam * ‖p.1‖ := by
  change ‖lam • p.1‖ = lam * ‖p.1‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]

/-- The second-quantized photon dilation. -/
def fockDilation (lam : ℝ) (hlam : 0 < lam) : PhotonFock ≃ₗᵢ[ℂ] PhotonFock :=
  fockScaled (photonDilationData lam hlam)

/-- The photon dilation on the radiation graph. -/
def radiationDilation (lam : ℝ) (hlam : 0 < lam) :
    RadiationGraphSpace ≃L[ℂ] RadiationGraphSpace :=
  radiationScaled (photonDilationData lam hlam) hlam (photonDilation_momentum lam hlam)

/-- The photon dilation on weighted kernels. -/
def kernelDilation (lam : ℝ) (hlam : 0 < lam) :
    WeightedPhotonKernel ≃L[ℂ] WeightedPhotonKernel :=
  kernelScaled (photonDilationData lam hlam) hlam (photonDilation_momentum lam hlam)

theorem radiationGraphInclusion_dilation (lam : ℝ) (hlam : 0 < lam) (q : RadiationGraphSpace) :
    radiationGraphInclusion (radiationDilation lam hlam q) =
      fockDilation lam hlam (radiationGraphInclusion q) := rfl

theorem radiationGraphDerivative_dilation (lam : ℝ) (hlam : 0 < lam) (q : RadiationGraphSpace) :
    radiationGraphDerivative (radiationDilation lam hlam q) =
      (Real.sqrt lam : ℂ)⁻¹ • fockDilation lam hlam (radiationGraphDerivative q) := rfl

theorem kernelDilation_fst (lam : ℝ) (hlam : 0 < lam) (k : WeightedPhotonKernel) :
    (kernelDilation lam hlam k).val.1 = photonDilation lam hlam k.val.1 := rfl

theorem kernelDilation_snd (lam : ℝ) (hlam : 0 < lam) (k : WeightedPhotonKernel) :
    (kernelDilation lam hlam k).val.2 = (Real.sqrt lam : ℂ) • photonDilation lam hlam k.val.2 :=
  rfl

theorem kernelAnnihilation_dilation (lam : ℝ) (hlam : 0 < lam) (k : WeightedPhotonKernel)
    (q : RadiationGraphSpace) :
    kernelAnnihilation (kernelDilation lam hlam k) (radiationDilation lam hlam q) =
      fockDilation lam hlam (kernelAnnihilation k q) :=
  kernelAnnihilation_scaled (photonDilationData lam hlam) hlam (photonDilation_momentum lam hlam)
    k q

theorem kernelCreation_dilation (lam : ℝ) (hlam : 0 < lam) (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelCreation C (kernelDilation lam hlam k) (radiationDilation lam hlam q) =
      fockDilation lam hlam (kernelCreation C k q) :=
  kernelCreation_scaled (photonDilationData lam hlam) hlam (photonDilation_momentum lam hlam)
    C k q

/-- Dilation covariance of the Segal field on the radiation graph. -/
theorem kernelField_dilation (lam : ℝ) (hlam : 0 < lam) (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelField C (kernelDilation lam hlam k) (radiationDilation lam hlam q) =
      fockDilation lam hlam (kernelField C k q) :=
  kernelField_scaled (photonDilationData lam hlam) hlam (photonDilation_momentum lam hlam) C k q

end Dilation

end GptLean.TransformationsFock
