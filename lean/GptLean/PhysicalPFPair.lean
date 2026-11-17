import GptLean.PhysicalPFObservables
import GptLean.PhysicalEnsembleTests
import GptLean.PhysicalPairTests

/-!
The physical density-current pair of a finite-energy positive normal
state is independent of the chosen spectral source. Every bounded scalar
density test and every bounded scalar current-component test is identified
with the same normal graph observable before applying L1 separation.
-/

noncomputable section

namespace GptLean.PhysicalPFSource

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalSourceCoordinates PhysicalPairSpace
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure)
  (M : ℝ) (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)
  (i : Fin N) (W : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (k : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hk : ∀ b, AEStronglyMeasurable (k b) volume)
  (hb : ∀ b, ∀ᵐ z ∂volume, ‖k b z‖ ≤ M)

variable {B}

theorem Source.pair_tested_density {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : Source (Fin N × Fin 3) W B x)
    (he : (normalEnergy (Fin N × Fin 3) W C k hk M hb B S e).expectation x < ⊤)
    (a : PhysicalPairSpace.Position → ℝ) (ha : AEStronglyMeasurable a volume)
    {c : ℝ} (hc : ∀ᵐ z ∂volume, ‖a z‖ ≤ c) :
    (∫ z, a z * densityL1 (s.pair C M S e i W k hk hb he) z) =
      (N : ℝ) * ∑' n, ∫ z, a ((split i) z).1 *
        ‖inclusion (Fin N × Fin 3) W (s.vector n) z‖ ^ 2 :=
  PhysicalSourcePair.tested_density_ofEnsemble i
    (fun n => ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) W (s.vector n)))
    s.mass_hasSum.summable
    (fun b => s.operator_summable C k hk M hb S e he (ordinary (Fin N × Fin 3) W b))
    (fun b n => covariant (Fin N × Fin 3) W C k hk M hb e (i, b) (s.vector n))
    (fun b => s.operator_summable C k hk M hb S e he
      (covariant (Fin N × Fin 3) W C k hk M hb e (i, b))) a ha hc

theorem Source.pair_tested_current {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : Source (Fin N × Fin 3) W B x)
    (he : (normalEnergy (Fin N × Fin 3) W C k hk M hb B S e).expectation x < ⊤)
    (b : Fin 3) (a : PhysicalPairSpace.Position → ℝ) (ha : AEStronglyMeasurable a volume)
    {c : ℝ} (hc : ∀ᵐ z ∂volume, ‖a z‖ ≤ c) :
    (∫ z, a z * currentL1 (s.pair C M S e i W k hk hb he) z b) =
      (N : ℝ) * ∑' n, ∫ z, a ((split i) z).1 *
        (⟪inclusion (Fin N × Fin 3) W (s.vector n) z,
          covariant (Fin N × Fin 3) W C k hk M hb e (i, b) (s.vector n) z⟫_ℂ).re :=
  PhysicalSourcePair.tested_current_ofEnsemble i
    (fun n => ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) W (s.vector n)))
    s.mass_hasSum.summable
    (fun b => s.operator_summable C k hk M hb S e he (ordinary (Fin N × Fin 3) W b))
    (fun b n => covariant (Fin N × Fin 3) W C k hk M hb e (i, b) (s.vector n))
    (fun b => s.operator_summable C k hk M hb S e he
      (covariant (Fin N × Fin 3) W C k hk M hb e (i, b))) b a ha hc

private theorem real_inner_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : H) : (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := by
  simpa only [RCLike.re_to_complex] using (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm

theorem Source.pair_independent {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s t : Source (Fin N × Fin 3) W B x)
    (he : (normalEnergy (Fin N × Fin 3) W C k hk M hb B S e).expectation x < ⊤) :
    s.pair C M S e i W k hk hb he = t.pair C M S e i W k hk hb he := by
  apply pair_eq_of_bounded_spatial_tests
  · intro a
    have ha := a.measurable.comp_fst.comp_measurePreserving (split_measurePreserving i)
    have hc : ∀ᵐ z ∂volume, |a.weight ((split i) z).1| ≤ 1 :=
      ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using a.bounded ((split i) z).1
    have h := s.tested_inner_independent C k hk M hb S e t he
      (inclusion (Fin N × Fin 3) W) (inclusion (Fin N × Fin 3) W)
      (fun z => a.weight ((split i) z).1) ha 1 hc
    have hs := s.pair_tested_density C M S e i W k hk hb he a.weight a.measurable
      (ae_of_all _ a.bounded)
    have ht := t.pair_tested_density C M S e i W k hk hb he a.weight a.measurable
      (ae_of_all _ a.bounded)
    exact hs.trans ((congrArg (fun r : ℝ => (N : ℝ) * r)
      (by simpa only [real_inner_self] using h)).trans ht.symm)
  · intro b a
    have ha := a.measurable.comp_fst.comp_measurePreserving (split_measurePreserving i)
    have hc : ∀ᵐ z ∂volume, |a.weight ((split i) z).1| ≤ 1 :=
      ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using a.bounded ((split i) z).1
    have h := s.tested_inner_independent C k hk M hb S e t he
      (inclusion (Fin N × Fin 3) W) (covariant (Fin N × Fin 3) W C k hk M hb e (i, b))
      (fun z => a.weight ((split i) z).1) ha 1 hc
    have hs := s.pair_tested_current C M S e i W k hk hb he b a.weight a.measurable
      (ae_of_all _ a.bounded)
    have ht := t.pair_tested_current C M S e i W k hk hb he b a.weight a.measurable
      (ae_of_all _ a.bounded)
    exact hs.trans ((congrArg (fun r : ℝ => (N : ℝ) * r) h).trans ht.symm)

end GptLean.PhysicalPFSource
