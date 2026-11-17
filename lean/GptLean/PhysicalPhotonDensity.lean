import GptLean.PhysicalFockSectorEnergy
import GptLean.HardLayerCake

/-!
The actual photon momentum occupation density of a Fock vector. The
head-coordinate marginal of every symmetric sector is multiplied by its
particle count. Tonelli and permutation symmetry identify its full mass
with photon number and its frequency moment with radiation energy.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

section SectorDensity

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

def headDensity (n : ℕ) (u : Sector μ (n + 1))
    (z : Ω × (Fin n → Ω)) : ℝ≥0∞ :=
  ENNReal.ofReal (‖u.val ((MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => Ω) 0).symm z)‖ ^ 2)

theorem headDensity_measurable (n : ℕ) (u : Sector μ (n + 1)) :
    Measurable (headDensity μ n u) :=
  (((Lp.stronglyMeasurable u.val).measurable.comp
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0).symm.measurable).norm.pow_const 2).ennreal_ofReal

def sectorPhotonDensity (n : ℕ) (u : Sector μ (n + 1)) (p : Ω) : ℝ≥0∞ :=
  (n + 1 : ℝ≥0∞) * ∫⁻ k, headDensity μ n u (p, k) ∂SectorMeasure μ n

theorem sectorPhotonDensity_measurable (n : ℕ) (u : Sector μ (n + 1)) :
    Measurable (sectorPhotonDensity μ n u) :=
  (headDensity_measurable μ n u).lintegral_prod_right'.const_mul _

/-- Every measurable one-photon moment is the corresponding labelled
sector moment multiplied by the number of photons. -/
theorem sectorPhotonDensity_moment (n : ℕ) (u : Sector μ (n + 1))
    (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p * sectorPhotonDensity μ n u p ∂μ) =
      (n + 1 : ℝ≥0∞) * ∫⁻ k, f (k 0) * ENNReal.ofReal (‖u.val k‖ ^ 2)
        ∂SectorMeasure μ (n + 1) := by
  have hpoint (p : Ω) : f p * (∫⁻ k, headDensity μ n u (p, k) ∂SectorMeasure μ n) =
      ∫⁻ k, f p * headDensity μ n u (p, k) ∂SectorMeasure μ n :=
    (lintegral_const_mul _ ((headDensity_measurable μ n u).comp measurable_prodMk_left)).symm
  unfold sectorPhotonDensity
  simp_rw [mul_left_comm (f _) (n + 1 : ℝ≥0∞), hpoint]
  have hm : Measurable (fun z : Ω × (Fin n → Ω) => f z.1 * headDensity μ n u z) :=
    (hf.comp measurable_fst).mul (headDensity_measurable μ n u)
  have hi : Measurable (fun p : Ω => ∫⁻ k, f p * headDensity μ n u (p, k)
      ∂SectorMeasure μ n) := hm.lintegral_prod_right'
  rw [lintegral_const_mul _ hi]
  congr 1
  rw [← lintegral_prod _ hm.aemeasurable]
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
  rw [← hp.lintegral_comp_emb e.measurableEmbedding]
  apply lintegral_congr
  intro k
  simp only [headDensity, MeasurableEquiv.symm_apply_apply]
  rfl

end SectorDensity

theorem sectorPhotonDensity_mass (n : ℕ) (u : Sector photonMeasure (n + 1)) :
    (∫⁻ p, sectorPhotonDensity photonMeasure n u p ∂photonMeasure) =
      ENNReal.ofReal ((n + 1 : ℝ) * ‖u‖ ^ 2) := by
  have h := sectorPhotonDensity_moment photonMeasure n u (fun _ => 1) measurable_const
  simp only [one_mul, sector_mass_lintegral] at h
  rw [h, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one,
    ENNReal.ofReal_natCast, ENNReal.ofReal_one]

theorem sectorPhotonDensity_radiation (n : ℕ) (u : Sector photonMeasure (n + 1)) :
    (∫⁻ p, ENNReal.ofReal ‖p.1‖ * sectorPhotonDensity photonMeasure n u p ∂photonMeasure) =
      sectorRadiationForm (n + 1) u := by
  rw [sectorPhotonDensity_moment _ _ _ _ (measurable_fst.norm.ennreal_ofReal)]
  rw [sectorRadiationForm_eq_coordinate (0 : Fin (n + 1))]
  simp only [Nat.cast_add, Nat.cast_one, coordinateRadiationForm]

def photonDensity (u : PhotonFock) (p : PhotonMode) : ℝ≥0∞ :=
  ∑' n, sectorPhotonDensity photonMeasure n (u (n + 1)) p

theorem photonDensity_measurable (u : PhotonFock) : Measurable (photonDensity u) :=
  Measurable.tsum fun n => sectorPhotonDensity_measurable _ n _

theorem photonDensity_number (u : PhotonFock) :
    (∫⁻ p, photonDensity u p ∂photonMeasure) = photonNumberForm photonMeasure u := by
  have hsum : (∫⁻ p, photonDensity u p ∂photonMeasure) =
      ∑' n, ∫⁻ p, sectorPhotonDensity photonMeasure n (u (n + 1)) p ∂photonMeasure :=
    lintegral_tsum (fun n => (sectorPhotonDensity_measurable photonMeasure n (u (n + 1))).aemeasurable)
  rw [hsum]
  simp_rw [sectorPhotonDensity_mass]
  change (∑' n : ℕ, ENNReal.ofReal ((n + 1 : ℝ) * ‖u (n + 1)‖ ^ 2)) =
    ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * ‖u n‖ ^ 2)
  have hzero := tsum_eq_zero_add'
    (f := fun n : ℕ => ENNReal.ofReal ((n : ℝ) * ‖u n‖ ^ 2)) ENNReal.summable
  simpa only [Nat.cast_zero, zero_mul, ENNReal.ofReal_zero, zero_add, Nat.cast_add,
    Nat.cast_one] using hzero.symm

theorem photonDensity_radiation (u : PhotonFock) :
    (∫⁻ p, ENNReal.ofReal ‖p.1‖ * photonDensity u p ∂photonMeasure) = radiationForm u := by
  have hm (n : ℕ) : Measurable (fun p : PhotonMode => ENNReal.ofReal ‖p.1‖ *
      sectorPhotonDensity photonMeasure n (u (n + 1)) p) :=
    measurable_fst.norm.ennreal_ofReal.mul (sectorPhotonDensity_measurable _ n _)
  have hp (p : PhotonMode) : ENNReal.ofReal ‖p.1‖ * photonDensity u p =
      ∑' n, ENNReal.ofReal ‖p.1‖ * sectorPhotonDensity photonMeasure n (u (n + 1)) p :=
    ENNReal.tsum_mul_left.symm
  simp_rw [hp]
  have hsum := lintegral_tsum (μ := photonMeasure) (fun n => (hm n).aemeasurable)
  rw [hsum]
  simp_rw [sectorPhotonDensity_radiation]
  change (∑' n, sectorRadiationForm (n + 1) (u (n + 1))) =
    ∑' n, sectorRadiationForm n (u n)
  have hz : sectorRadiationForm 0 (u 0) = 0 := by
    simp [sectorRadiationForm, sectorDispersion]
  have hzero := tsum_eq_zero_add' (f := fun n => sectorRadiationForm n (u n)) ENNReal.summable
  simpa only [hz, zero_add] using hzero.symm

/-- The photon-density moment interface is now proved for actual Fock
vectors with finite radiation energy, allowing infinite total number. -/
theorem photonDensity_moments (u : PhotonFock) (hE : radiationForm u < ⊤) :
    HardLayerCake.HasPhotonDensity photonMeasure (fun p => ‖p.1‖) (photonDensity u)
      (fun κ => (∫⁻ p in {p | κ ≤ ‖p.1‖}, photonDensity u p ∂photonMeasure).toReal)
      (fun κ => (∫⁻ p in {p | ‖p.1‖ < κ}, ENNReal.ofReal ‖p.1‖ *
        photonDensity u p ∂photonMeasure).toReal)
      (radiationForm u).toReal where
  measurable := photonDensity_measurable u
  finite := by rwa [photonDensity_radiation]
  numHard_eq := fun _ => rfl
  Esoft_eq := fun _ => rfl
  Erad_eq := congrArg ENNReal.toReal (photonDensity_radiation u).symm

end GptLean.PhysicalFock
