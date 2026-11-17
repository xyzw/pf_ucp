import GptLean.PhysicalFockSectors
import GptLean.PhotonLocalizationLocalForms

/-!
Bounded symmetric momentum multipliers on the actual product-L² photon sectors
and their Hilbert direct sum. The integral and order formulas are derived from
the L² representatives and Parseval, rather than prescribed on a trace model.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalization
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

structure BoundedSymmetricWeight (C : ℝ) where
  value : ∀ n, (Fin n → Ω) → ℝ
  measurable : ∀ n, AEStronglyMeasurable (value n) (SectorMeasure μ n)
  bound : ∀ n k, |value n k| ≤ C
  symmetric : ∀ n (π : Equiv.Perm (Fin n)) k,
    value n (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π k) = value n k

namespace BoundedSymmetricWeight

variable {μ} {C : ℝ} (w : BoundedSymmetricWeight μ C)

def fullSector (n : ℕ) : FullSector μ n →L[ℂ] FullSector μ n :=
  realL2Multiplier (w.value n) (w.measurable n) C (ae_of_all _ (w.bound n))

omit [SigmaFinite μ] in
theorem fullSector_ae (n : ℕ) (u : FullSector μ n) :
    w.fullSector n u =ᵐ[SectorMeasure μ n] fun k => w.value n k • u k :=
  realL2Multiplier_apply _ _ _ _ _

theorem fullSector_symmetric (n : ℕ) (u : Sector μ n) :
    w.fullSector n u.val ∈ symmetricSubspace μ n := by
  intro π
  apply Lp.ext
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => μ) π
  filter_upwards [permutation_ae μ n π (w.fullSector n u.val),
    w.fullSector_ae n u.val, hp.quasiMeasurePreserving.ae (w.fullSector_ae n u.val),
    symmetric_ae μ n u π] with k hperm hv hvp hu
  change (permutation μ n π (w.fullSector n u.val)) k = (w.fullSector n u.val) k
  rw [hperm, hv]
  change (w.fullSector n u.val) (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) π k) = _
  rw [hvp, w.symmetric]
  exact congrArg (fun z => w.value n k • z) hu.symm

def sector (n : ℕ) : Sector μ n →L[ℂ] Sector μ n :=
  ((w.fullSector n).comp (sectorInclusion μ n).toContinuousLinearMap).codRestrict
    (symmetricSubspace μ n) (w.fullSector_symmetric n)

theorem sector_ae (n : ℕ) (u : Sector μ n) :
    (w.sector n u).val =ᵐ[SectorMeasure μ n] fun k => w.value n k • u.val k :=
  w.fullSector_ae n u.val

theorem sector_norm_le (n : ℕ) (u : Sector μ n) : ‖w.sector n u‖ ≤ C * ‖u‖ :=
  realL2Multiplier_norm_le (w.value n) (w.measurable n) C (ae_of_all _ (w.bound n)) u.val

def operator (hC : 0 ≤ C) : Fock μ →L[ℂ] Fock μ :=
  LinearMap.mkContinuous
    { toFun u := ⟨fun n => w.sector n (u n),
        ((lp.memℓp u).norm.const_mul C).mono (fun n => by
          simpa only [Pi.mul_apply, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg hC (norm_nonneg _))] using w.sector_norm_le n (u n))⟩
      map_add' u v := by
        apply lp.ext
        funext n
        exact map_add (w.sector n) (u n) (v n)
      map_smul' c u := by
        apply lp.ext
        funext n
        exact map_smul (w.sector n) c (u n) }
    C (fun u => by
      change ‖(⟨fun n => w.sector n (u n), _⟩ : Fock μ)‖ ≤ C * ‖u‖
      have h := lp.norm_mono (p := 2) (by norm_num)
        (x := (⟨fun n => w.sector n (u n),
          ((lp.memℓp u).norm.const_mul C).mono (fun n => by
            simpa only [Pi.mul_apply, Real.norm_eq_abs,
              abs_of_nonneg (mul_nonneg hC (norm_nonneg _))] using w.sector_norm_le n (u n))⟩ : Fock μ))
        (y := (C : ℂ) • u) (fun n => by
          simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hC] using w.sector_norm_le n (u n))
      simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC] using h)

@[simp] theorem operator_apply (hC : 0 ≤ C) (u : Fock μ) (n : ℕ) :
    w.operator hC u n = w.sector n (u n) := rfl

theorem sector_integrable (n : ℕ) (u : Sector μ n) :
    Integrable (fun k => w.value n k * ‖u.val k‖ ^ 2) (SectorMeasure μ n) := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u.val)).mp
    (Lp.memLp u.val)
  apply (hi.const_mul C).mono' ((w.measurable n).mul ((Lp.aestronglyMeasurable u.val).norm.pow 2))
  exact ae_of_all _ fun k => by
    change |w.value n k * ‖u.val k‖ ^ 2| ≤ C * ‖u.val k‖ ^ 2
    simpa only [abs_mul, abs_pow, abs_norm] using
      mul_le_mul_of_nonneg_right (w.bound n k) (sq_nonneg ‖u.val k‖)

theorem sector_inner (n : ℕ) (u : Sector μ n) :
    (⟪u, w.sector n u⟫_ℂ).re = ∫ k, w.value n k * ‖u.val k‖ ^ 2 ∂SectorMeasure μ n := by
  change (⟪u.val, w.fullSector n u.val⟫_ℂ).re = _
  rw [L2.inner_def]
  have hre := Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) u.val (w.fullSector n u.val))
  change (∫ k, inner ℂ (u.val k) (w.fullSector n u.val k) ∂SectorMeasure μ n).re = _
  rw [← show (∫ k, (inner ℂ (u.val k) (w.fullSector n u.val k)).re ∂SectorMeasure μ n) =
    (∫ k, inner ℂ (u.val k) (w.fullSector n u.val k) ∂SectorMeasure μ n).re from hre]
  apply integral_congr_ae
  filter_upwards [w.fullSector_ae n u.val] with k hk
  rw [hk, inner_smul_right_eq_smul]
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

theorem operator_inner_hasSum (hC : 0 ≤ C) (u : Fock μ) :
    HasSum (fun n => ∫ k, w.value n k * ‖(u n).val k‖ ^ 2 ∂SectorMeasure μ n)
      (⟪u, w.operator hC u⟫_ℂ).re := by
  have h := Complex.reCLM.hasSum (lp.hasSum_inner u (w.operator hC u))
  change HasSum (fun n => (⟪u n, w.sector n (u n)⟫_ℂ).re)
    (⟪u, w.operator hC u⟫_ℂ).re at h
  simpa only [w.sector_inner] using h

theorem operator_inner_nonneg (hC : 0 ≤ C) (hw : ∀ n k, 0 ≤ w.value n k) (u : Fock μ) :
    0 ≤ (⟪u, w.operator hC u⟫_ℂ).re := by
  rw [← (w.operator_inner_hasSum hC u).tsum_eq]
  exact tsum_nonneg fun n => integral_nonneg fun k => mul_nonneg (hw n k) (sq_nonneg _)

theorem operator_inner_ofReal (hC : 0 ≤ C) (hw : ∀ n k, 0 ≤ w.value n k) (u : Fock μ) :
    ENNReal.ofReal (⟪u, w.operator hC u⟫_ℂ).re =
      ∑' n, ∫⁻ k, ENNReal.ofReal (w.value n k) * ENNReal.ofReal (‖(u n).val k‖ ^ 2)
        ∂SectorMeasure μ n := by
  rw [← (w.operator_inner_hasSum hC u).tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun k =>
      mul_nonneg (hw n k) (sq_nonneg _)) (w.operator_inner_hasSum hC u).summable]
  congr 1
  funext n
  rw [ofReal_integral_eq_lintegral_ofReal (w.sector_integrable n (u n))
    (ae_of_all _ fun k => mul_nonneg (hw n k) (sq_nonneg _))]
  simp only [ENNReal.ofReal_mul (hw n _)]

theorem operator_inner_mono {D : ℝ} (v : BoundedSymmetricWeight μ D)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hwv : ∀ n k, w.value n k ≤ v.value n k) (u : Fock μ) :
    (⟪u, w.operator hC u⟫_ℂ).re ≤ (⟪u, v.operator hD u⟫_ℂ).re := by
  rw [← (w.operator_inner_hasSum hC u).tsum_eq, ← (v.operator_inner_hasSum hD u).tsum_eq]
  apply Summable.tsum_le_tsum _ (w.operator_inner_hasSum hC u).summable (v.operator_inner_hasSum hD u).summable
  intro n
  exact integral_mono_ae (w.sector_integrable n (u n)) (v.sector_integrable n (u n))
    (ae_of_all _ fun k => mul_le_mul_of_nonneg_right (hwv n k) (sq_nonneg _))

end BoundedSymmetricWeight
end GptLean.PhysicalFock
