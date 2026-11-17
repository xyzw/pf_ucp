import GptLean.PhysicalPFDomain
import GptLean.PhysicalNormalSpectral
import GptLean.PhysicalEnsemblePair
import GptLean.PhysicalFockSeparable

/-!
Finite normal Pauli--Fierz energy supplies actual common-domain spectral
vectors. The form graph estimate makes their reference norms square
summable, hence every ordinary and covariant derivative is square
summable. The density-current pair is then constructed by the proved
electronic H1 and spectator Fubini maps.
-/

noncomputable section

namespace GptLean.PhysicalPFSource

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalPFRadiation
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

private theorem norm_prod_sq_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] (u : E) (v : F) :
    ‖(u, v)‖ ^ 2 ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [Prod.norm_def]
  rcases le_total ‖u‖ ‖v‖ with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (sq_nonneg _)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (sq_nonneg _)

private theorem summable_operator_sq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (u : ℕ → E) (hu : Summable (fun n => ‖u n‖ ^ 2)) :
    Summable (fun n => ‖L (u n)‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (hu.mul_left (‖L‖ ^ 2))
  intro n
  exact (pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm (u n)) 2).trans_eq (mul_pow _ _ _)

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

theorem reference_norm_sq_le (u : Reference I V) :
    ‖u‖ ^ 2 ≤ (formComparisonConstant I C κ hκ M hbound e * (1 + Real.sqrt 2)) ^ 2 *
      (‖inclusion I V u‖ ^ 2 + energy I V C κ hκ M hbound e u) := by
  have h₁ := pow_le_pow_left₀ (norm_nonneg u)
    (reference_norm_le_energyGraph I V C κ hκ M hbound e u) 2
  have h₂ : ‖energyGraphMap I V C κ hκ M hbound e u‖ ^ 2 ≤
      ‖inclusion I V u‖ ^ 2 + energy I V C κ hκ M hbound e u :=
    (norm_prod_sq_le (inclusion I V u) (energyOutput I V C κ hκ M hbound e u)).trans_eq
      (congrArg (fun r : ℝ => ‖inclusion I V u‖ ^ 2 + r)
        (energyOutput_norm_sq I V C κ hκ M hbound e u))
  exact (h₁.trans_eq (mul_pow _ _ _)).trans
    (mul_le_mul_of_nonneg_left h₂ (sq_nonneg _))

/-- A positive spectral source on the actual common physical domain. -/
structure Source (x : B.Trace (WaveSpace I)) where
  vector : ℕ → Reference I V
  hasSum : HasSum (fun n => (B.realization (WaveSpace I)).rank.rankOne
    (inclusion I V (vector n))) x

theorem source_exists {x : B.Trace (WaveSpace I)}
    (hx : x ∈ (B.realization (WaveSpace I)).rank.positive)
    (he : (normalEnergy I V C κ hκ M hbound B S e).expectation x < ⊤) :
    Nonempty (Source I V B x) := by
  obtain ⟨v, hv⟩ := (B.realization (WaveSpace I)).spectral x hx
  have hd (n : ℕ) : ∃ u : Reference I V, inclusion I V u = v n :=
    (normalEnergy_rankOne_finite_iff I V C κ hκ M hbound B S e (v n)).mp
      (PhysicalNormalSpectral.source_form_finite
        (normalEnergy I V C κ hκ M hbound B S e) hv he n)
  choose u hu using hd
  exact ⟨⟨u, hv.congr_fun (fun n => congrArg (B.realization (WaveSpace I)).rank.rankOne
    (hu n))⟩⟩

variable {I V B}

theorem Source.mass_hasSum {x : B.Trace (WaveSpace I)} (s : Source I V B x) :
    HasSum (fun n => ‖inclusion I V (s.vector n)‖ ^ 2)
      ((B.realization (WaveSpace I)).rank.trace x) := by
  simpa only [(B.realization (WaveSpace I)).rank.trace_rankOne] using
    (B.realization (WaveSpace I)).rank.trace.hasSum s.hasSum

theorem Source.energy_hasSum {x : B.Trace (WaveSpace I)} (s : Source I V B x)
    (he : (normalEnergy I V C κ hκ M hbound B S e).expectation x < ⊤) :
    HasSum (fun n => energy I V C κ hκ M hbound e (s.vector n))
      ((normalEnergy I V C κ hκ M hbound B S e).expectation x).toReal := by
  have h := PhysicalNormalSpectral.source_form_hasSum
    (normalEnergy I V C κ hκ M hbound B S e) s.hasSum he
  apply h.congr_fun
  intro n
  exact ((congrArg ENNReal.toReal
    (normalEnergy_rankOne I V C κ hκ M hbound B S e (s.vector n))).trans
      (ENNReal.toReal_ofReal (energy_nonneg I V C κ hκ M hbound e (s.vector n)))).symm

theorem Source.reference_summable {x : B.Trace (WaveSpace I)} (s : Source I V B x)
    (he : (normalEnergy I V C κ hκ M hbound B S e).expectation x < ⊤) :
    Summable (fun n => ‖s.vector n‖ ^ 2) := by
  have h := s.mass_hasSum.summable.add
    (s.energy_hasSum C κ hκ M hbound S e he).summable
  exact Summable.of_nonneg_of_le (fun n => sq_nonneg _)
    (fun n => reference_norm_sq_le I V C κ hκ M hbound e (s.vector n))
    (h.mul_left ((formComparisonConstant I C κ hκ M hbound e * (1 + Real.sqrt 2)) ^ 2))

theorem Source.operator_summable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {x : B.Trace (WaveSpace I)} (s : Source I V B x)
    (he : (normalEnergy I V C κ hκ M hbound B S e).expectation x < ⊤)
    (L : Reference I V →L[ℂ] F) : Summable (fun n => ‖L (s.vector n)‖ ^ 2) := by
  apply summable_operator_sq (E := Reference I V) (F := F) L s.vector
  exact s.reference_summable C κ hκ M hbound S e he

section Pair

variable {N : ℕ} (i : Fin N) (W : Position (Fin N × Fin 3) → ℝ)
  (k : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hk : ∀ b, AEStronglyMeasurable (k b) volume)
  (hb : ∀ b, ∀ᵐ z ∂volume, ‖k b z‖ ≤ M)

/-- The actual density-current Banach pair of a common-domain source. -/
def Source.pair {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : Source (Fin N × Fin 3) W B x)
    (he : (normalEnergy (Fin N × Fin 3) W C k hk M hb B S e).expectation x < ⊤) :
    PhysicalPairSpace.Pair :=
  PhysicalSourcePair.ofEnsemble i
    (fun n => ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) W (s.vector n)))
    s.mass_hasSum.summable
    (fun b => s.operator_summable C k hk M hb S e he (ordinary (Fin N × Fin 3) W b))
    (fun a n => covariant (Fin N × Fin 3) W C k hk M hb e (i, a) (s.vector n))
    (fun a => s.operator_summable C k hk M hb S e he
      (covariant (Fin N × Fin 3) W C k hk M hb e (i, a)))

theorem Source.pair_mass {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : Source (Fin N × Fin 3) W B x)
    (he : (normalEnergy (Fin N × Fin 3) W C k hk M hb B S e).expectation x < ⊤) :
    (∫ z, PhysicalPairSpace.densityL1 (s.pair C M S e i W k hk hb he) z) =
      (N : ℝ) * (B.realization (WaveSpace (Fin N × Fin 3))).rank.trace x := by
  exact (PhysicalSourcePair.integral_density_ofEnsemble i
    (fun n => ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) W (s.vector n)))
    s.mass_hasSum.summable
    (fun b => s.operator_summable C k hk M hb S e he (ordinary (Fin N × Fin 3) W b))
    (fun a n => covariant (Fin N × Fin 3) W C k hk M hb e (i, a) (s.vector n))
    (fun a => s.operator_summable C k hk M hb S e he
      (covariant (Fin N × Fin 3) W C k hk M hb e (i, a)))).trans
        (congrArg (fun r : ℝ => (N : ℝ) * r) s.mass_hasSum.tsum_eq)

end Pair

end GptLean.PhysicalPFSource
