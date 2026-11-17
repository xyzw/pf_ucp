import GptLean.PhysicalFockSectors
import GptLean.PhotonKernelLocalization
import Mathlib.MeasureTheory.Integral.Prod

/-!
Actual one-photon tensor insertion and symmetric sector creation.

The tensor product is the product of the L² representatives on product
measure, transported through the head/tail coordinate equivalence.
Creation is normalized symmetric projection of this actual insertion.
Annihilation on each adjacent pair of sectors is its Hilbert adjoint.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

section Product

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {μ : Measure Ω} {ν : Measure Ξ} [SigmaFinite μ] [SigmaFinite ν]

omit [SigmaFinite μ] [SigmaFinite ν] in
private theorem product_memLp (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    MemLp (fun z : Ω × Ξ => f z.1 * g z.2) 2 (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun z : Ω × Ξ => f z.1 * g z.2) (μ.prod ν) :=
    (Lp.aestronglyMeasurable f).comp_fst.mul (Lp.aestronglyMeasurable g).comp_snd
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hg := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  simpa only [norm_mul, mul_pow] using hf.mul_prod hg

def productL2 (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  (product_memLp f g).toLp _

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem productL2_ae (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productL2 f g =ᵐ[μ.prod ν] fun z => f z.1 * g z.2 :=
  (product_memLp f g).coeFn_toLp

theorem productL2_norm (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    ‖productL2 f g‖ = ‖f‖ * ‖g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral, mul_pow,
    PhotonKernelLocalization.l2_norm_sq_eq_integral f,
    PhotonKernelLocalization.l2_norm_sq_eq_integral g, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [productL2_ae f g] with z hz
  rw [hz, norm_mul, mul_pow]

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem productL2_add_right (f : Lp ℂ 2 μ) (g h : Lp ℂ 2 ν) :
    productL2 f (g + h) = productL2 f g + productL2 f h := by
  apply Lp.ext
  filter_upwards [productL2_ae f (g + h), productL2_ae f g, productL2_ae f h,
    (Measure.quasiMeasurePreserving_snd (μ := μ)).ae (Lp.coeFn_add g h),
    Lp.coeFn_add (productL2 f g) (productL2 f h)] with z ha hb hc hd he
  rw [ha, he, Pi.add_apply, hb, hc, hd, Pi.add_apply, mul_add]

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem productL2_smul_right (f : Lp ℂ 2 μ) (c : ℂ) (g : Lp ℂ 2 ν) :
    productL2 f (c • g) = c • productL2 f g := by
  apply Lp.ext
  filter_upwards [productL2_ae f (c • g), productL2_ae f g,
    (Measure.quasiMeasurePreserving_snd (μ := μ)).ae (Lp.coeFn_smul c g),
    Lp.coeFn_smul c (productL2 f g)] with z ha hb hc hd
  rw [ha, hd, Pi.smul_apply, hb, hc, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

def productL2Right (f : Lp ℂ 2 μ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    { toFun := productL2 f
      map_add' := productL2_add_right f
      map_smul' := productL2_smul_right f }
    ‖f‖ (fun g => (productL2_norm f g).le)

@[simp] theorem productL2Right_apply (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productL2Right f g = productL2 f g := rfl

end Product

section Sectors

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

/-- Put one new photon in the head coordinate of the product wave function. -/
def tensorInsertion (n : ℕ) (f : Lp ℂ 2 μ) :
    FullSector μ n →L[ℂ] FullSector μ (n + 1) :=
  (Lp.compMeasurePreservingₗᵢ ℂ
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0)
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0)).toContinuousLinearMap.comp
      (productL2Right f)

theorem tensorInsertion_norm (n : ℕ) (f : Lp ℂ 2 μ) (u : FullSector μ n) :
    ‖tensorInsertion μ n f u‖ = ‖f‖ * ‖u‖ := by
  change ‖(Lp.compMeasurePreservingₗᵢ ℂ _ _) (productL2 f u)‖ = _
  rw [LinearIsometry.norm_map, productL2_norm]

theorem tensorInsertion_ae (n : ℕ) (f : Lp ℂ 2 μ) (u : FullSector μ n) :
    tensorInsertion μ n f u =ᵐ[SectorMeasure μ (n + 1)] fun k =>
      f (k 0) * u (fun i => k (Fin.succ i)) := by
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
  filter_upwards [Lp.coeFn_compMeasurePreserving (productL2 f u) hp,
    hp.quasiMeasurePreserving.ae (productL2_ae f u)] with k hk ht
  exact hk.trans ht

/-- The normalized creation operator between adjacent symmetric sectors. -/
def creationSector (n : ℕ) (f : Lp ℂ 2 μ) : Sector μ n →L[ℂ] Sector μ (n + 1) :=
  (Real.sqrt (n + 1 : ℝ) : ℂ) •
    ((symmetricSubspace μ (n + 1)).orthogonalProjectionOnto.comp
      ((tensorInsertion μ n f).comp (symmetricSubspace μ n).subtypeL))

theorem creationSector_norm_le (n : ℕ) (f : Lp ℂ 2 μ) (u : Sector μ n) :
    ‖creationSector μ n f u‖ ≤ Real.sqrt (n + 1 : ℝ) * ‖f‖ * ‖u‖ := by
  change ‖(Real.sqrt (n + 1 : ℝ) : ℂ) •
    (symmetricSubspace μ (n + 1)).orthogonalProjectionOnto (tensorInsertion μ n f u.val)‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (n + 1 : ℝ) * ‖tensorInsertion μ n f u.val‖ :=
      mul_le_mul_of_nonneg_left
        ((symmetricSubspace μ (n + 1)).norm_orthogonalProjectionOnto_apply_le _) (Real.sqrt_nonneg _)
    _ = _ := by rw [tensorInsertion_norm, mul_assoc]; rfl

theorem creationSector_opNorm_le (n : ℕ) (f : Lp ℂ 2 μ) :
    ‖creationSector μ n f‖ ≤ Real.sqrt (n + 1 : ℝ) * ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (creationSector_norm_le μ n f)

/-- Annihilation is the actual adjoint of normalized symmetric insertion. -/
def annihilationSector (n : ℕ) (f : Lp ℂ 2 μ) : Sector μ (n + 1) →L[ℂ] Sector μ n :=
  (creationSector μ n f).adjoint

theorem annihilationSector_duality (n : ℕ) (f : Lp ℂ 2 μ)
    (u : Sector μ n) (v : Sector μ (n + 1)) :
    ⟪creationSector μ n f u, v⟫_ℂ = ⟪u, annihilationSector μ n f v⟫_ℂ :=
  ((creationSector μ n f).adjoint_inner_right u v).symm

theorem annihilationSector_norm_le (n : ℕ) (f : Lp ℂ 2 μ) (u : Sector μ (n + 1)) :
    ‖annihilationSector μ n f u‖ ≤ (Real.sqrt (n + 1 : ℝ) * ‖f‖) * ‖u‖ := by
  apply (annihilationSector μ n f).le_opNorm u |>.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (ContinuousLinearMap.adjoint.norm_map _).le.trans (creationSector_opNorm_le μ n f)

end Sectors

end GptLean.PhysicalFock
