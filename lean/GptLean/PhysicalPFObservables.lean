import GptLean.PhysicalPFSource
import GptLean.PhysicalGraphSourceObservable
import GptLean.PhysicalSourceTests

/-!
Normal bilinear observables of the actual Pauli--Fierz reference domain.
Bounded spatial tests are represented by the constructed L2 multiplier.
The source formula follows from polarization of closed positive forms.
-/

noncomputable section

namespace GptLean.PhysicalPFSource

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalGraphForms PhotonLocalizationChannel PhotonLocalization
open scoped ENNReal NNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem multiplier_tested_inner (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (c : ℝ) (hb : ∀ᵐ z ∂μ, |a z| ≤ c) (v w : Lp H 2 μ) :
    (⟪v, realL2Multiplier a ha c hb w⟫_ℂ).re =
      ∫ z, a z * (⟪v z, w z⟫_ℂ).re ∂μ := by
  rw [L2.inner_def]
  have hr := Complex.reCLM.integral_comp_comm
    (L2.integrable_inner (𝕜 := ℂ) v (realL2Multiplier a ha c hb w))
  change (∫ z, ⟪v z, realL2Multiplier a ha c hb w z⟫_ℂ ∂μ).re = _
  exact hr.symm.trans (integral_congr_ae (by
    filter_upwards [realL2Multiplier_apply a ha c hb w] with z hz
    rw [hz, inner_smul_right_eq_smul]
    change (a z • (⟪v z, w z⟫_ℂ)).re = a z * (⟪v z, w z⟫_ℂ).re
    simp only [Complex.smul_re, smul_eq_mul]))

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

def coerciveGraph : CoerciveGraph (Reference I V) (WaveSpace I) (EnergyOutput I) where
  value := inclusion I V
  output := energyOutput I V C κ hκ M hbound e
  injective := inclusion_injective I V
  constant := ⟨formComparisonConstant I C κ hκ M hbound e * (1 + Real.sqrt 2),
    mul_nonneg (formComparisonConstant_nonneg I C κ hκ M hbound e) (by positivity)⟩
  bound u := reference_norm_le_energyGraph I V C κ hκ M hbound e u

variable {I V B}

theorem Source.inner_hasSum {F : Type} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    {x : B.Trace (WaveSpace I)} (s : Source I V B x)
    (he : (normalEnergy I V C κ hκ M hbound B S e).expectation x < ⊤)
    (L R : Reference I V →L[ℂ] F) :
    HasSum (fun n => (⟪L (s.vector n), R (s.vector n)⟫_ℂ).re)
      ((coerciveGraph I V C κ hκ M hbound e).crossValue B S L R x) :=
  (coerciveGraph I V C κ hκ M hbound e).crossValue_source_hasSum B S L R
    s.hasSum (s.reference_summable C κ hκ M hbound S e he)

theorem Source.tested_inner_hasSum {x : B.Trace (WaveSpace I)} (s : Source I V B x)
    (he : (normalEnergy I V C κ hκ M hbound B S e).expectation x < ⊤)
    (L R : Reference I V →L[ℂ] WaveSpace I)
    (a : Position I → ℝ) (ha : AEStronglyMeasurable a volume)
    (c : ℝ) (hb : ∀ᵐ z ∂volume, |a z| ≤ c) :
    HasSum (fun n => ∫ z, a z * (⟪L (s.vector n) z, R (s.vector n) z⟫_ℂ).re)
      ((coerciveGraph I V C κ hκ M hbound e).crossValue B S L
        ((realL2Multiplier a ha c hb).comp R) x) := by
  exact (s.inner_hasSum C κ hκ M hbound S e he L
    ((realL2Multiplier a ha c hb).comp R)).congr_fun
      (fun n => (multiplier_tested_inner a ha c hb (L (s.vector n)) (R (s.vector n))).symm)

theorem Source.tested_inner_independent {x : B.Trace (WaveSpace I)} (s t : Source I V B x)
    (he : (normalEnergy I V C κ hκ M hbound B S e).expectation x < ⊤)
    (L R : Reference I V →L[ℂ] WaveSpace I)
    (a : Position I → ℝ) (ha : AEStronglyMeasurable a volume)
    (c : ℝ) (hb : ∀ᵐ z ∂volume, |a z| ≤ c) :
    (∑' n, ∫ z, a z * (⟪L (s.vector n) z, R (s.vector n) z⟫_ℂ).re) =
      ∑' n, ∫ z, a z * (⟪L (t.vector n) z, R (t.vector n) z⟫_ℂ).re :=
  (s.tested_inner_hasSum C κ hκ M hbound S e he L R a ha c hb).tsum_eq.trans
    (t.tested_inner_hasSum C κ hκ M hbound S e he L R a ha c hb).tsum_eq.symm

end GptLean.PhysicalPFSource
