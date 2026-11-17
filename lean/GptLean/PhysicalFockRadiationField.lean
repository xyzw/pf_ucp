import GptLean.PhysicalFockAnnihilation
import GptLean.PhysicalFockRadiationCore

/-!
The actual annihilation operator on the complete radiation graph.

Its output is formed from the adjacent-sector adjoints. The radiation
estimate proves square summability, so no output-space or field bound is
an assumption. This is the constant-kernel component of spatial field
calculus on the same physical Fock model.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

theorem radiationGraph_energy (q : RadiationGraphSpace) :
    radiationForm (radiationGraphInclusion q) =
      ENNReal.ofReal (‖radiationGraphDerivative q‖ ^ 2) := by
  obtain ⟨u, hu, hv⟩ := radiationRoot.mem_graph_iff.mp q.property
  change radiationForm q.val.1 = ENNReal.ofReal (‖q.val.2‖ ^ 2)
  rw [← hu, ← hv]
  exact radiationRoot_energy u

theorem radiationGraph_finite (q : RadiationGraphSpace) :
    radiationForm (radiationGraphInclusion q) < ⊤ := by
  rw [radiationGraph_energy]
  exact ENNReal.ofReal_lt_top

theorem annihilation_sector_tsum_bound (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (u : PhotonFock) (hE : radiationForm u < ⊤) :
    (∑' n, ENNReal.ofReal (‖annihilationSector photonMeasure n f (u (n + 1))‖ ^ 2)) ≤
      ENNReal.ofReal (‖g‖ ^ 2) * radiationForm u := by
  calc
    _ ≤ ∑' n, ENNReal.ofReal (‖g‖ ^ 2) * sectorRadiationForm (n + 1) (u (n + 1)) :=
      ENNReal.tsum_le_tsum fun n => annihilationSector_radiation_bound n f g hfg
        (u (n + 1)) ((ENNReal.le_tsum (n + 1)).trans_lt hE)
    _ = ENNReal.ofReal (‖g‖ ^ 2) *
        ∑' n, sectorRadiationForm (n + 1) (u (n + 1)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (‖g‖ ^ 2) * radiationForm u := by
      gcongr
      exact ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective
        (fun n => sectorRadiationForm n (u n))

def annihilationGraphOutput (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (q : RadiationGraphSpace) : PhotonFock := by
  let a := fun n => annihilationSector photonMeasure n f (radiationGraphInclusion q (n + 1))
  have ht : (∑' n, ENNReal.ofReal (‖a n‖ ^ 2)) ≠ ⊤ :=
    ((annihilation_sector_tsum_bound f g hfg (radiationGraphInclusion q)
      (radiationGraph_finite q)).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (radiationGraph_finite q))).ne
  have hs : Summable (fun n => ‖a n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal ht
  exact ⟨a, memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs)⟩

@[simp] theorem annihilationGraphOutput_coordinate (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (q : RadiationGraphSpace) (n : ℕ) :
    annihilationGraphOutput f g hfg q n =
      annihilationSector photonMeasure n f (radiationGraphInclusion q (n + 1)) := rfl

theorem annihilationGraphOutput_norm_le (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (q : RadiationGraphSpace) :
    ‖annihilationGraphOutput f g hfg q‖ ≤ ‖g‖ * ‖radiationGraphDerivative q‖ := by
  have h := annihilation_sector_tsum_bound f g hfg (radiationGraphInclusion q)
    (radiationGraph_finite q)
  have hm : (∑' n, ENNReal.ofReal (‖annihilationGraphOutput f g hfg q n‖ ^ 2)) =
      ENNReal.ofReal (‖annihilationGraphOutput f g hfg q‖ ^ 2) := by
    simpa only [weightedForm, one_mul] using
      massForm_eq (Sector photonMeasure) (annihilationGraphOutput f g hfg q)
  change (∑' n, ENNReal.ofReal (‖annihilationGraphOutput f g hfg q n‖ ^ 2)) ≤ _ at h
  rw [hm, radiationGraph_energy, ← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow] at h
  have hs := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg (‖g‖ * ‖radiationGraphDerivative q‖))).mp h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hs

/-- The actual annihilation map, continuous for the radiation graph norm. -/
def annihilationRadiation (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p) :
    RadiationGraphSpace →L[ℂ] PhotonFock :=
  LinearMap.mkContinuous
    { toFun := annihilationGraphOutput f g hfg
      map_add' q r := by
        apply lp.ext
        funext n
        exact map_add (annihilationSector photonMeasure n f) _ _
      map_smul' c q := by
        apply lp.ext
        funext n
        exact map_smul (annihilationSector photonMeasure n f) c _ }
    (‖g‖ * ‖radiationGraphDerivative‖) (fun q =>
      (annihilationGraphOutput_norm_le f g hfg q).trans
        (by nlinarith only [radiationGraphDerivative.le_opNorm q, norm_nonneg g]))

theorem annihilationRadiation_norm_le (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (q : RadiationGraphSpace) :
    ‖annihilationRadiation f g hfg q‖ ≤ ‖g‖ * ‖radiationGraphDerivative q‖ :=
  annihilationGraphOutput_norm_le f g hfg q

@[simp] theorem annihilationRadiation_coordinate (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (q : RadiationGraphSpace) (n : ℕ) :
    annihilationRadiation f g hfg q n =
      annihilationSector photonMeasure n f (radiationGraphInclusion q (n + 1)) := rfl

end GptLean.PhysicalFock
