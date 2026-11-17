import GptLean.RepresentabilityCoherentOnePhoton
import GptLean.PhysicalFockRadiationSlices
import GptLean.PhysicalFockRadiationGraph

/-!
Radiation and number identities are derived by summing the actual shifted
annihilation forms. No Weyl radiation estimate is added to the background.
All energies remain extended nonnegative reals until finiteness is proved.
-/

noncomputable section
set_option Elab.async false

namespace GptLean.Representability

open MeasureTheory GptLean.PhysicalFock GptLean.PhotonLocalizationFormBounds
open scoped ENNReal InnerProductSpace

private theorem coherent_fockForm_tsum {h : Type*} (q : ℕ → h → ℝ≥0∞)
    (slice : (m : ℕ) → Fin m → ℕ → h) :
    fockForm (fun u => ∑' k, q k u) slice = ∑' k, fockForm (q k) slice := by
  unfold fockForm sectorForm
  simp_rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  calc
    _ = ∑' m, ∑' i : Fin m, ∑' k, ∑' a, q k (slice m i a) :=
      tsum_congr (fun _ => tsum_congr (fun _ => ENNReal.tsum_comm))
    _ = ∑' m, ∑' k, ∑' i : Fin m, ∑' a, q k (slice m i a) :=
      tsum_congr (fun _ => ENNReal.tsum_comm)
    _ = _ := ENNReal.tsum_comm

/-- This uses only the constructed annihilation sectors and Fock slices. -/
theorem sum_annihilationForm_eq_fockForm (q : OnePhotonFormFamily) (u : PhotonFock) :
    (∑' i, annihilationForm photonMeasure (q i) u) =
      fockForm (onePhotonFamilyValue q) (fockSlices u) := by
  simp_rw [← fockSlices_annihilationForm]
  exact (coherent_fockForm_tsum
    (fun i g => ENNReal.ofReal (‖⟪q i, g⟫_ℂ‖ ^ 2)) (fockSlices u)).symm

theorem sum_annihilationForm_eq_radiationForm (u : PhotonFock) :
    (∑' i, annihilationForm photonMeasure (radiationFamily i) u) = radiationForm u :=
  (sum_annihilationForm_eq_fockForm radiationFamily u).trans (fockSlices_radiationForm u)

theorem sum_annihilationForm_eq_numberForm (u : PhotonFock) :
    (∑' i, annihilationForm photonMeasure (numberFamily i) u) =
      photonNumberForm photonMeasure u := by
  rw [sum_annihilationForm_eq_fockForm,
    show onePhotonFamilyValue numberFamily =
      (fun f : Lp ℂ 2 photonMeasure => ENNReal.ofReal (‖f‖ ^ 2)) from
      funext numberFamily_value]
  exact fockSlices_number u

namespace ConcreteWeylLaw

variable (W : ConcreteWeylLaw photonMeasure)

theorem coherent_radiation (f : Lp ℂ 2 photonMeasure) :
    radiationForm (W.coherent photonMeasure f) = onePhotonFamilyValue radiationFamily f := by
  rw [← sum_annihilationForm_eq_radiationForm]
  simp only [W.coherent_annihilationForm photonMeasure, onePhotonFamilyValue]

theorem coherent_photonNumber (f : Lp ℂ 2 photonMeasure) :
    photonNumberForm photonMeasure (W.coherent photonMeasure f) =
      ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [← sum_annihilationForm_eq_numberForm]
  simp only [W.coherent_annihilationForm photonMeasure]
  exact numberFamily_value f

/-- Displacement adds precisely its one-photon energy to a fixed-number
auxiliary vector. Vanishing cross terms follow from sector orthogonality. -/
theorem displacedOnePhoton_radiation (f : Lp ℂ 2 photonMeasure)
    (z : Sector photonMeasure 1) :
    radiationForm (W.displacedOnePhoton photonMeasure f z) =
      radiationForm (lp.single 2 1 z) +
        onePhotonFamilyValue radiationFamily f * ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← sum_annihilationForm_eq_radiationForm]
  simp_rw [W.displacedOnePhoton_annihilationForm photonMeasure]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
    sum_annihilationForm_eq_radiationForm]
  rfl

theorem displacedOnePhoton_photonNumber (f : Lp ℂ 2 photonMeasure)
    (z : Sector photonMeasure 1) :
    photonNumberForm photonMeasure (W.displacedOnePhoton photonMeasure f z) =
      photonNumberForm photonMeasure (lp.single 2 1 z) +
        ENNReal.ofReal (‖f‖ ^ 2) * ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← sum_annihilationForm_eq_numberForm]
  simp_rw [W.displacedOnePhoton_annihilationForm photonMeasure]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, sum_annihilationForm_eq_numberForm]
  exact congrArg (fun E => photonNumberForm photonMeasure (lp.single 2 1 z) +
    E * ENNReal.ofReal (‖z‖ ^ 2)) (numberFamily_value f)

theorem coherent_radiation_domain (f : Lp ℂ 2 photonMeasure)
    (hf : onePhotonFamilyValue radiationFamily f < ⊤) :
    W.coherent photonMeasure f ∈ radiationRoot.domain :=
  radiationRoot_domain_of_finite _ (by rwa [W.coherent_radiation])

theorem displacedOnePhoton_radiation_domain (f : Lp ℂ 2 photonMeasure)
    (z : Sector photonMeasure 1)
    (hf : onePhotonFamilyValue radiationFamily f < ⊤)
    (hz : radiationForm (lp.single 2 1 z) < ⊤) :
    W.displacedOnePhoton photonMeasure f z ∈ radiationRoot.domain := by
  apply radiationRoot_domain_of_finite
  rw [W.displacedOnePhoton_radiation]
  exact ENNReal.add_lt_top.mpr
    ⟨hz, ENNReal.mul_lt_top hf ENNReal.ofReal_lt_top⟩

end ConcreteWeylLaw
end GptLean.Representability
