import GptLean.PhysicalFockCreation
import GptLean.PhysicalFockRadiationGraph

/-!
The energy carried by each labelled photon in a symmetric sector.

Permutation invariance makes the labelled energies equal. Their sum is
exactly the physical sector radiation form, including infinite values.
For finite energy the square-root weight in a single coordinate gives
an actual L² vector, without imposing any output-vector assumption.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

def coordinateRadiationForm {n : ℕ} (i : Fin n) (u : Sector photonMeasure n) : ℝ≥0∞ :=
  ∫⁻ k, ENNReal.ofReal (‖(k i).1‖) * ENNReal.ofReal (‖u.val k‖ ^ 2)
    ∂SectorMeasure photonMeasure n

theorem coordinateRadiationForm_eq {n : ℕ} (i j : Fin n) (u : Sector photonMeasure n) :
    coordinateRadiationForm i u = coordinateRadiationForm j u := by
  let π := Equiv.swap i j
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => photonMeasure) π
  have he (k : Fin n → PhotonMode) : e k i = k j := by
    simpa only [π, Equiv.swap_apply_right] using
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => PhotonMode) π k j
  unfold coordinateRadiationForm
  rw [← hp.lintegral_comp_emb e.measurableEmbedding]
  apply lintegral_congr_ae
  filter_upwards [symmetric_ae photonMeasure n u π] with k hk
  change ENNReal.ofReal ‖(e k i).1‖ * ENNReal.ofReal (‖u.val (e k)‖ ^ 2) =
    ENNReal.ofReal ‖(k j).1‖ * ENNReal.ofReal (‖u.val k‖ ^ 2)
  rw [he, hk]
  rfl

theorem sectorRadiationForm_sum_coordinates (n : ℕ) (u : Sector photonMeasure n) :
    sectorRadiationForm n u = ∑ i : Fin n, coordinateRadiationForm i u := by
  unfold sectorRadiationForm sectorDispersion coordinateRadiationForm
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _), Finset.sum_mul]
  apply lintegral_finsetSum'
  intro i _
  exact (measurable_pi_apply i).fst.norm.ennreal_ofReal.aemeasurable.mul
    ((Lp.aestronglyMeasurable u.val).norm.pow 2).aemeasurable.ennreal_ofReal

theorem sectorRadiationForm_eq_coordinate {n : ℕ} (i : Fin n) (u : Sector photonMeasure n) :
    sectorRadiationForm n u = (n : ℝ≥0∞) * coordinateRadiationForm i u := by
  rw [sectorRadiationForm_sum_coordinates]
  calc
    ∑ j : Fin n, coordinateRadiationForm j u = ∑ _ : Fin n, coordinateRadiationForm i u :=
      Finset.sum_congr rfl fun j _ => coordinateRadiationForm_eq j i u
    _ = _ := by simp

theorem coordinateRadiationForm_le {n : ℕ} (i : Fin n) (u : Sector photonMeasure n) :
    coordinateRadiationForm i u ≤ sectorRadiationForm n u := by
  rw [sectorRadiationForm_sum_coordinates]
  exact Finset.single_le_sum (f := fun j : Fin n => coordinateRadiationForm j u)
    (fun _ _ => zero_le) (Finset.mem_univ i)

theorem exists_coordinateRoot_of_finite {n : ℕ} (i : Fin n) (u : Sector photonMeasure n)
    (hE : sectorRadiationForm n u < ⊤) :
    ∃ z : FullSector photonMeasure n, ∀ᵐ k ∂SectorMeasure photonMeasure n,
      z k = (Real.sqrt (‖(k i).1‖) : ℂ) * u.val k := by
  let f : (Fin n → PhotonMode) → ℂ :=
    fun k => (Real.sqrt (‖(k i).1‖) : ℂ) * u.val k
  have hc : Measurable (fun k : Fin n → PhotonMode => (Real.sqrt (‖(k i).1‖) : ℂ)) := by
    fun_prop
  have hm : AEStronglyMeasurable f (SectorMeasure photonMeasure n) :=
    hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u.val)
  have he (k : Fin n → PhotonMode) : ‖f k‖ ^ 2 = ‖(k i).1‖ * ‖u.val k‖ ^ 2 := by
    simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (norm_nonneg _)]
  have hf : MemLp f 2 (SectorMeasure photonMeasure n) := by
    apply (memLp_two_iff_integrable_sq_norm hm).mpr
    refine ⟨hm.norm.pow 2, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun k => sq_nonneg (‖f k‖))).mpr
    simpa only [he, ENNReal.ofReal_mul (norm_nonneg _), coordinateRadiationForm] using
      (coordinateRadiationForm_le i u).trans_lt hE
  exact ⟨hf.toLp f, hf.coeFn_toLp⟩

theorem coordinateRadiationForm_eq_root_norm {n : ℕ} (i : Fin n)
    (u : Sector photonMeasure n) (z : FullSector photonMeasure n)
    (hz : ∀ᵐ k ∂SectorMeasure photonMeasure n,
      z k = (Real.sqrt (‖(k i).1‖) : ℂ) * u.val k) :
    coordinateRadiationForm i u = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral,
    ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable z)).mp (Lp.memLp z))
      (ae_of_all _ fun k => sq_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [hz] with k hk
  rw [hk]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (norm_nonneg _),
    ENNReal.ofReal_mul (norm_nonneg _)]

theorem sectorRadiationForm_eq_coordinateRoot_norm {n : ℕ} (i : Fin n)
    (u : Sector photonMeasure n) (z : FullSector photonMeasure n)
    (hz : ∀ᵐ k ∂SectorMeasure photonMeasure n,
      z k = (Real.sqrt (‖(k i).1‖) : ℂ) * u.val k) :
    sectorRadiationForm n u = ENNReal.ofReal ((n : ℝ) * ‖z‖ ^ 2) := by
  rw [sectorRadiationForm_eq_coordinate i, coordinateRadiationForm_eq_root_norm i u z hz,
    ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

end GptLean.PhysicalFock
