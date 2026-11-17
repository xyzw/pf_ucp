import GptLean.PhysicalPhotonDensity

/-!
All nonnegative one-photon moments of the same momentum density, before
and after a positive spectral sum. This includes hard number and soft
radiation moments and does not require finite total photon number.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def coordinatePhotonMoment (q : PhotonMode → ℝ≥0∞) {n : ℕ} (i : Fin n)
    (u : Sector photonMeasure n) : ℝ≥0∞ :=
  ∫⁻ k, q (k i) * ENNReal.ofReal (‖u.val k‖ ^ 2) ∂SectorMeasure photonMeasure n

theorem coordinatePhotonMoment_eq (q : PhotonMode → ℝ≥0∞) {n : ℕ}
    (i j : Fin n) (u : Sector photonMeasure n) :
    coordinatePhotonMoment q i u = coordinatePhotonMoment q j u := by
  let π := Equiv.swap i j
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => photonMeasure) π
  have he (k : Fin n → PhotonMode) : e k i = k j := by
    simpa only [π, Equiv.swap_apply_right] using
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => PhotonMode) π k j
  unfold coordinatePhotonMoment
  rw [← hp.lintegral_comp_emb e.measurableEmbedding]
  apply lintegral_congr_ae
  filter_upwards [symmetric_ae photonMeasure n u π] with k hk
  change q (e k i) * ENNReal.ofReal (‖u.val (e k)‖ ^ 2) =
    q (k j) * ENNReal.ofReal (‖u.val k‖ ^ 2)
  rw [he, hk]
  rfl

def sectorPhotonMoment (q : PhotonMode → ℝ≥0∞) (n : ℕ)
    (u : Sector photonMeasure n) : ℝ≥0∞ :=
  ∫⁻ k, (∑ i, q (k i)) * ENNReal.ofReal (‖u.val k‖ ^ 2) ∂SectorMeasure photonMeasure n

theorem sectorPhotonMoment_sum (q : PhotonMode → ℝ≥0∞) (hq : Measurable q)
    (n : ℕ) (u : Sector photonMeasure n) :
    sectorPhotonMoment q n u = ∑ i : Fin n, coordinatePhotonMoment q i u := by
  unfold sectorPhotonMoment coordinatePhotonMoment
  simp_rw [Finset.sum_mul]
  apply lintegral_finsetSum'
  intro i _
  exact (hq.comp (measurable_pi_apply i)).aemeasurable.mul
    ((Lp.aestronglyMeasurable u.val).norm.pow 2).aemeasurable.ennreal_ofReal

theorem sectorPhotonMoment_eq_coordinate (q : PhotonMode → ℝ≥0∞) (hq : Measurable q)
    {n : ℕ} (i : Fin n) (u : Sector photonMeasure n) :
    sectorPhotonMoment q n u = (n : ℝ≥0∞) * coordinatePhotonMoment q i u := by
  rw [sectorPhotonMoment_sum q hq]
  calc
    ∑ j : Fin n, coordinatePhotonMoment q j u = ∑ _ : Fin n, coordinatePhotonMoment q i u :=
      Finset.sum_congr rfl fun j _ => coordinatePhotonMoment_eq q j i u
    _ = _ := by simp

theorem sectorPhotonDensity_moment_eq (q : PhotonMode → ℝ≥0∞) (hq : Measurable q)
    (n : ℕ) (u : Sector photonMeasure (n + 1)) :
    (∫⁻ p, q p * sectorPhotonDensity photonMeasure n u p ∂photonMeasure) =
      sectorPhotonMoment q (n + 1) u := by
  rw [sectorPhotonDensity_moment _ _ _ q hq,
    sectorPhotonMoment_eq_coordinate q hq (0 : Fin (n + 1))]
  simp only [Nat.cast_add, Nat.cast_one, coordinatePhotonMoment]

def photonMoment (q : PhotonMode → ℝ≥0∞) (u : PhotonFock) : ℝ≥0∞ :=
  ∑' n, sectorPhotonMoment q n (u n)

/-- The occupation density gives every nonnegative one-photon moment
of the actual symmetric Fock wave function. -/
theorem photonDensity_moment (q : PhotonMode → ℝ≥0∞) (hq : Measurable q)
    (u : PhotonFock) :
    (∫⁻ p, q p * photonDensity u p ∂photonMeasure) = photonMoment q u := by
  have hm (n : ℕ) : Measurable (fun p : PhotonMode => q p *
      sectorPhotonDensity photonMeasure n (u (n + 1)) p) :=
    hq.mul (sectorPhotonDensity_measurable _ n _)
  have hp (p : PhotonMode) : q p * photonDensity u p =
      ∑' n, q p * sectorPhotonDensity photonMeasure n (u (n + 1)) p :=
    ENNReal.tsum_mul_left.symm
  simp_rw [hp]
  have hsum := lintegral_tsum (μ := photonMeasure) (fun n => (hm n).aemeasurable)
  rw [hsum]
  simp_rw [sectorPhotonDensity_moment_eq q hq]
  change (∑' n, sectorPhotonMoment q (n + 1) (u (n + 1))) =
    ∑' n, sectorPhotonMoment q n (u n)
  have hz : sectorPhotonMoment q 0 (u 0) = 0 := by simp [sectorPhotonMoment]
  have hzero := tsum_eq_zero_add' (f := fun n => sectorPhotonMoment q n (u n)) ENNReal.summable
  simpa only [hz, zero_add] using hzero.symm

theorem photonMoment_one (u : PhotonFock) :
    photonMoment (fun _ => 1) u = photonNumberForm photonMeasure u := by
  rw [← photonDensity_moment _ measurable_const, ← photonDensity_number u]
  simp only [one_mul]

theorem photonMoment_frequency (u : PhotonFock) :
    photonMoment (fun p => ENNReal.ofReal ‖p.1‖) u = radiationForm u := by
  rw [← photonDensity_moment _ measurable_fst.norm.ennreal_ofReal, photonDensity_radiation]

def ensemblePhotonDensity (v : ℕ → PhotonFock) (p : PhotonMode) : ℝ≥0∞ :=
  ∑' n, photonDensity (v n) p

theorem ensemblePhotonDensity_measurable (v : ℕ → PhotonFock) :
    Measurable (ensemblePhotonDensity v) := Measurable.tsum fun n => photonDensity_measurable (v n)

theorem ensemblePhotonDensity_moment (q : PhotonMode → ℝ≥0∞) (hq : Measurable q)
    (v : ℕ → PhotonFock) :
    (∫⁻ p, q p * ensemblePhotonDensity v p ∂photonMeasure) = ∑' n, photonMoment q (v n) := by
  have hp (p : PhotonMode) : q p * ensemblePhotonDensity v p = ∑' n, q p * photonDensity (v n) p :=
    ENNReal.tsum_mul_left.symm
  simp_rw [hp]
  have hm (n : ℕ) : Measurable (fun p => q p * photonDensity (v n) p) :=
    hq.mul (photonDensity_measurable (v n))
  rw [lintegral_tsum (μ := photonMeasure) (fun n => (hm n).aemeasurable)]
  exact tsum_congr fun n => photonDensity_moment q hq (v n)

theorem ensemblePhotonDensity_number (v : ℕ → PhotonFock) :
    (∫⁻ p, ensemblePhotonDensity v p ∂photonMeasure) =
      ∑' n, photonNumberForm photonMeasure (v n) := by
  simpa only [one_mul, photonMoment_one] using
    ensemblePhotonDensity_moment (fun _ => 1) measurable_const v

theorem ensemblePhotonDensity_radiation (v : ℕ → PhotonFock) :
    (∫⁻ p, ENNReal.ofReal ‖p.1‖ * ensemblePhotonDensity v p ∂photonMeasure) =
      ∑' n, radiationForm (v n) := by
  simpa only [photonMoment_frequency] using
    ensemblePhotonDensity_moment (fun p => ENNReal.ofReal ‖p.1‖)
      measurable_fst.norm.ennreal_ofReal v

end GptLean.PhysicalFock
