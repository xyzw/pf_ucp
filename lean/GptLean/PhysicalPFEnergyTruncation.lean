import GptLean.PhysicalPFDecomposition
import GptLean.PhysicalFockPhysicalForms
import GptLean.PhysicalFockFormTruncation
import GptLean.PhysicalOnePhotonFourier
import GptLean.PhotonLocalizationCurrentPassage

/-!
The physical radiation prefixes recover the full Pauli–Fierz energy on
positive normal operators, including infinite energies. The ambient
extension used by trace-limit arguments is defined by those same
prefixes, so its lower semicontinuity and recovery hold on the whole
real trace space.
-/

noncomputable section

namespace GptLean.PhysicalPFEnergyTruncation

open MeasureTheory PhysicalFock PhysicalNormalTrace PhysicalClosedForms
  PhotonLocalizationChannel PhotonLocalizationFormBounds RemovalState
  PhysicalCovariantKinetic
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option Elab.async false

variable (N : ℕ) (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)

def calculus := fullFormCalculus BF C B PhysicalOnePhotonFourier.fourier N

def radiationPrefix (k : ℕ) : PositiveForm (B.traceData (H := Wave N)) :=
  (calculus N B BF C).observable (finiteFamily radiationFamily k)

theorem radiation_recovery {x : B.Trace (Wave N)}
    (hx : x ∈ (B.realization (Wave N)).rank.positive) :
    (PhysicalPFDecomposition.radiation N B).expectation x =
      ⨆ k, (radiationPrefix N B BF C k).expectation x := by
  have h := (calculus N B BF C).radiation_eq_iSup B.normal (fun _ hx => hx)
    radiationFamily (finiteFamily radiationFamily)
    (fun i u => ⟪radiationFamily i, PhysicalOnePhotonFourier.fourier u⟫_ℂ)
    (fun _ => rfl)
    (fun k u => finiteFamily_value radiationFamily k (PhysicalOnePhotonFourier.fourier u)) hx
  exact (fullFormCalculus_radiation_eq BF C B PhysicalOnePhotonFourier.fourier N hx).symm.trans h

variable
  (κ : Index N → PhysicalPFReference.Position (Index N) → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

def truncatedEnergy (k : ℕ) (x : B.Trace (Wave N)) : ℝ≥0∞ :=
  (PhysicalPFDecomposition.kinetic N B S C κ hκ M hbound e).expectation x +
    (PhysicalPFDecomposition.coulomb N B).expectation x +
      (radiationPrefix N B BF C k).expectation x

def ambientEnergy (x : B.Trace (Wave N)) : ℝ≥0∞ :=
  ⨆ k, truncatedEnergy N B S BF C κ hκ M hbound e k x

theorem truncatedEnergy_lsc (k : ℕ) :
    LowerSemicontinuous (truncatedEnergy N B S BF C κ hκ M hbound e k) :=
  ((PhotonLocalizationCurrent.expectation_lowerSemicontinuous
    (PhysicalPFDecomposition.kinetic N B S C κ hκ M hbound e)).add
      (PhotonLocalizationCurrent.expectation_lowerSemicontinuous
        (PhysicalPFDecomposition.coulomb N B))).add
          (PhotonLocalizationCurrent.expectation_lowerSemicontinuous (radiationPrefix N B BF C k))

theorem ambientEnergy_lsc :
    LowerSemicontinuous (ambientEnergy N B S BF C κ hκ M hbound e) :=
  lowerSemicontinuous_iSup (truncatedEnergy_lsc N B S BF C κ hκ M hbound e)

theorem ambientEnergy_eq_iSup (x : B.Trace (Wave N)) :
    ambientEnergy N B S BF C κ hκ M hbound e x =
      ⨆ k, truncatedEnergy N B S BF C κ hκ M hbound e k x := rfl

private theorem recover_sum (a b r : ℝ≥0∞) (p : ℕ → ℝ≥0∞)
    (h : r = ⨆ k, p k) : (⨆ k, a + b + p k) = a + b + r := by
  rw [h, ENNReal.add_iSup]

theorem ambientEnergy_eq_physical {x : B.Trace (Wave N)}
    (hx : x ∈ (B.realization (Wave N)).rank.positive) :
    ambientEnergy N B S BF C κ hκ M hbound e x =
      (PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation x := by
  exact (recover_sum _ _ _ _ (radiation_recovery N B BF C hx)).trans
    (PhysicalPFDecomposition.normal_decomposition N B S C κ hκ M hbound e hx).symm

private theorem ofReal_sum_toReal (a b c : ℝ≥0∞)
    (ha : a < ⊤) (hb : b < ⊤) (hc : c < ⊤) :
    a + b + c = ENNReal.ofReal (a.toReal + b.toReal + c.toReal) := by
  rw [ENNReal.ofReal_add (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    ENNReal.toReal_nonneg,
    ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal ha.ne, ENNReal.ofReal_toReal hb.ne, ENNReal.ofReal_toReal hc.ne]

theorem truncatedEnergy_of_finite (k : ℕ) (x : B.Trace (Wave N))
    (hk : (PhysicalPFDecomposition.kinetic N B S C κ hκ M hbound e).expectation x < ⊤)
    (hp : (PhysicalPFDecomposition.coulomb N B).expectation x < ⊤)
    (hr : (radiationPrefix N B BF C k).expectation x < ⊤) :
    truncatedEnergy N B S BF C κ hκ M hbound e k x =
      ENNReal.ofReal (((PhysicalPFDecomposition.kinetic N B S C κ hκ M hbound e).expectation x).toReal +
        ((PhysicalPFDecomposition.coulomb N B).expectation x).toReal +
          ((radiationPrefix N B BF C k).expectation x).toReal) :=
  ofReal_sum_toReal _ _ _ hk hp hr

theorem kinetic_le_energy {x : B.Trace (Wave N)}
    (hx : x ∈ (B.realization (Wave N)).rank.positive) :
    (PhysicalPFDecomposition.kinetic N B S C κ hκ M hbound e).expectation x ≤
      (PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation x := by
  rw [PhysicalPFDecomposition.normal_decomposition N B S C κ hκ M hbound e hx]
  exact (le_add_right le_rfl).trans (le_add_right le_rfl)

theorem coulomb_le_energy {x : B.Trace (Wave N)}
    (hx : x ∈ (B.realization (Wave N)).rank.positive) :
    (PhysicalPFDecomposition.coulomb N B).expectation x ≤
      (PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation x := by
  rw [PhysicalPFDecomposition.normal_decomposition N B S C κ hκ M hbound e hx]
  exact (le_add_left le_rfl).trans (le_add_right le_rfl)

theorem radiation_le_energy {x : B.Trace (Wave N)}
    (hx : x ∈ (B.realization (Wave N)).rank.positive) :
    (PhysicalPFDecomposition.radiation N B).expectation x ≤
      (PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation x := by
  rw [PhysicalPFDecomposition.normal_decomposition N B S C κ hκ M hbound e hx]
  exact le_add_left le_rfl

theorem full_form {x : B.Trace (Wave N)}
    (hx : x ∈ (B.realization (Wave N)).rank.positive)
    (he : (PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation x < ⊤) :
    ((PhysicalPFDecomposition.energy N B S C κ hκ M hbound e).expectation x).toReal =
      ((PhysicalPFDecomposition.kinetic N B S C κ hκ M hbound e).expectation x).toReal +
        ((PhysicalPFDecomposition.coulomb N B).expectation x).toReal +
          ((PhysicalPFDecomposition.radiation N B).expectation x).toReal := by
  have hk := (kinetic_le_energy N B S C κ hκ M hbound e hx).trans_lt he
  have hp := (coulomb_le_energy N B S C κ hκ M hbound e hx).trans_lt he
  have hr := (radiation_le_energy N B S C κ hκ M hbound e hx).trans_lt he
  have hs := ofReal_sum_toReal _ _ _ hk hp hr
  have heq := (PhysicalPFDecomposition.normal_decomposition N B S C κ hκ M hbound e hx).trans hs
  exact (congrArg ENNReal.toReal heq).trans
    (ENNReal.toReal_ofReal (add_nonneg (add_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg) ENNReal.toReal_nonneg))

end GptLean.PhysicalPFEnergyTruncation
