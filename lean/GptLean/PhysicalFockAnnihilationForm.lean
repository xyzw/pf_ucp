import GptLean.PhysicalFockSliceContraction
import GptLean.PhysicalFockFiniteOperators

/-!
The extended annihilation form on the actual Fock Hilbert space.

Its value is the sum of the squared adjacent-sector outputs. The actual
one-photon slices identify it with the additive Fock form of a one-photon
rank-one observable, including vectors with infinite form value.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

def annihilationForm (f : Lp ℂ 2 μ) (u : Fock μ) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (‖annihilationSector μ n f (u (n + 1))‖ ^ 2)

theorem annihilationFinite_coordinate (M n : ℕ) (f : Lp ℂ 2 μ) (u : Fock μ) :
    annihilationFinite μ M f u n =
      if n < M then annihilationSector μ n f (u (n + 1)) else 0 := by
  classical
  have hoff (m : ℕ) (h : n ≠ m) : annihilationBlock μ m f u n = 0 := by
    change (lp.single 2 m (annihilationSector μ m f (u (m + 1)))) n = 0
    exact lp.single_apply_ne _ _ _ h
  simp only [annihilationFinite, sum_apply, lp.coeFn_sum, Finset.sum_apply]
  by_cases hn : n < M
  · rw [ite_eq_left hn, Finset.sum_eq_single n]
    · exact lp.single_apply_self 2 n (annihilationSector μ n f (u (n + 1)))
    · intro m _ hmn
      exact hoff m (Ne.symm hmn)
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hn))
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro m hm
    exact hoff m (fun h => hn (h ▸ Finset.mem_range.mp hm))

theorem annihilationFinite_norm_sq (M : ℕ) (f : Lp ℂ 2 μ) (u : Fock μ) :
    ‖annihilationFinite μ M f u‖ ^ 2 =
      ∑ n ∈ Finset.range M, ‖annihilationSector μ n f (u (n + 1))‖ ^ 2 := by
  have hs := coordinate_mass_hasSum (Sector μ) (annihilationFinite μ M f u)
  rw [← hs.tsum_eq]
  rw [tsum_eq_sum (s := Finset.range M)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [annihilationFinite_coordinate, ite_eq_left (Finset.mem_range.mp hn)]
  · intro n hn
    rw [annihilationFinite_coordinate, ite_eq_right (fun h => hn (Finset.mem_range.mpr h)),
      norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem annihilationForm_eq_iSup (f : Lp ℂ 2 μ) (u : Fock μ) :
    annihilationForm μ f u = ⨆ M : ℕ,
      ∑ n ∈ Finset.range M, ENNReal.ofReal (‖annihilationSector μ n f (u (n + 1))‖ ^ 2) :=
  ENNReal.tsum_eq_iSup_nat

/-- Bounded number truncations increase to the full extended annihilation form. -/
theorem annihilationForm_eq_iSup_finite (f : Lp ℂ 2 μ) (u : Fock μ) :
    annihilationForm μ f u = ⨆ M : ℕ, ENNReal.ofReal (‖annihilationFinite μ M f u‖ ^ 2) := by
  rw [annihilationForm_eq_iSup]
  apply iSup_congr
  intro M
  rw [annihilationFinite_norm_sq,
    ENNReal.ofReal_sum_of_nonneg (fun n _ => sq_nonneg _)]

theorem annihilationSector_slices_ennreal (n : ℕ) (f : Lp ℂ 2 photonMeasure)
    (u : Sector photonMeasure (n + 1)) :
    (∑' a, ENNReal.ofReal ((n + 1 : ℝ) * ‖⟪f, onePhotonSlices n u a⟫_ℂ‖ ^ 2)) =
      ENNReal.ofReal (‖annihilationSector photonMeasure n f u‖ ^ 2) := by
  have h := annihilationSector_slices_hasSum n f u
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => by positivity) h.summable, h.tsum_eq]

/-- The actual rank-one one-photon form has precisely the constructed annihilation value. -/
theorem fockSlices_annihilationForm (f : Lp ℂ 2 photonMeasure) (u : PhotonFock) :
    PhotonLocalizationFormBounds.fockForm (fun g : Lp ℂ 2 photonMeasure =>
      ENNReal.ofReal (‖⟪f, g⟫_ℂ‖ ^ 2)) (fockSlices u) = annihilationForm photonMeasure f u := by
  unfold PhotonLocalizationFormBounds.fockForm PhotonLocalizationFormBounds.sectorForm
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [fockSlices, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
  change (∑' n, ∑ _i : Fin (n + 1), ∑' a,
    ENNReal.ofReal (‖⟪f, onePhotonSlices n (u (n + 1)) a⟫_ℂ‖ ^ 2)) = _
  apply tsum_congr
  intro n
  rw [Finset.sum_const, nsmul_eq_mul]
  have hn : ((Finset.univ : Finset (Fin (n + 1))).card : ℝ≥0∞) =
      ENNReal.ofReal (n + 1 : ℝ) := by norm_num [ENNReal.ofReal_add]
  rw [hn, ← ENNReal.tsum_mul_left]
  simp_rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (n + 1 : ℝ))]
  exact annihilationSector_slices_ennreal n f (u (n + 1))

end GptLean.PhysicalFock
