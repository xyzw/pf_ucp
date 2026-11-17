import GptLean.PhysicalCoulombReferenceCore
import GptLean.PhysicalFreeForm
import GptLean.PhysicalPFDomain
import GptLean.PhysicalNormalFormOrder

/-!
Uniform comparisons between the actual free and Pauli--Fierz positive
forms on their common Coulomb reference domain. Constants are obtained
from the constructed bounded maps and the proved inverse graph bounds.
-/

noncomputable section

namespace GptLean.PhysicalPFComparison

open MeasureTheory PhysicalFock PhysicalClosedForms PhysicalNormalTrace
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

private def operatorBound {Q H : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L : Q →L[ℂ] H) : ℝ := ‖L‖ + 1

private theorem operatorBound_nonneg {Q H : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L : Q →L[ℂ] H) : 0 ≤ operatorBound L := by
  exact add_nonneg (norm_nonneg L) zero_le_one

private theorem norm_le_operatorBound {Q H : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L : Q →L[ℂ] H) (q : Q) : ‖L q‖ ≤ operatorBound L * ‖q‖ := by
  exact (L.le_opNorm q).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg q))

private theorem operator_sq_of_bound {Q H K : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (L : Q →L[ℂ] H) (A : Q →L[ℂ] K) (C : ℝ)
    (h : ∀ q, ‖q‖ ≤ C * ‖A q‖) (q : Q) :
    ‖L q‖ ^ 2 ≤ (operatorBound L * C) ^ 2 * ‖A q‖ ^ 2 := by
  have hb := (norm_le_operatorBound L q).trans
    (mul_le_mul_of_nonneg_left (h q) (operatorBound_nonneg L))
  have hs := pow_le_pow_left₀ (norm_nonneg (L q)) hb 2
  simpa only [mul_pow, mul_assoc] using hs

private theorem pair_norm_sq_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (x : E) (y : F) : ‖(x, y)‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  change (max ‖x‖ ‖y‖) ^ 2 ≤ _
  rcases le_total ‖x‖ ‖y‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖x‖]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg ‖y‖]

private theorem comparison_from_finite {V Q : Type*}
    (L R M : V → ℝ≥0∞) (f : Q → V) (b : ℝ≥0∞) (hb : b ≠ 0)
    (hfinite : ∀ v, R v < ⊤ → ∃ q, f q = v)
    (hgraph : ∀ q, L (f q) ≤ b * (R (f q) + M (f q))) (v : V) :
    L v ≤ b * (R v + M v) := by
  by_cases hv : R v < ⊤
  · obtain ⟨q, rfl⟩ := hfinite v hv
    exact hgraph q
  · have ht : R v = ⊤ := top_unique (not_lt.mp hv)
    rw [ht, top_add, ENNReal.mul_top hb]
    exact le_top

abbrev Index (N : ℕ) := Fin N × Fin 3
abbrev potential (N : ℕ) (c : ℝ) : EuclideanSpace ℝ (Index N) → ℝ :=
  fun x => c * PhysicalCoulombH1.potential N x

variable (N : ℕ) (c : ℝ) (hc : 0 ≤ c)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : Index N → EuclideanSpace ℝ (Index N) → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)

local instance freeReferenceNormedSpace : NormedSpace ℂ (PhysicalFreeForm.Reference (Index N)) :=
  (PhysicalFreeReferenceCore.freeSubspace (Index N)).normedSpace

local instance pfReferenceNormedSpace : NormedSpace ℂ (PhysicalCoulombReferenceCore.Reference N c) :=
  PhysicalPFReference.referenceNormedSpace (Index N) (potential N c)

def pfOutputOnFree (e : ℝ) :
    PhysicalFreeForm.Reference (Index N) →L[ℂ] PhysicalPFReference.EnergyOutput (Index N) :=
  (PhysicalPFReference.energyOutput (Index N) (potential N c) C κ hκ M hbound e).comp
    (PhysicalCoulombReferenceCore.referenceEquiv N c hc).toContinuousLinearMap

def freeOutputOnPF :
    PhysicalCoulombReferenceCore.Reference N c →L[ℂ] PhysicalFreeForm.EnergyOutput (Index N) :=
  (PhysicalFreeForm.energyOutput (Index N)).comp (PhysicalCoulombReferenceCore.forget N c)

def reverseConstant (e : ℝ) : ℝ := (operatorBound (Q := PhysicalFreeForm.Reference (Index N))
    (H := PhysicalPFReference.EnergyOutput (Index N))
    (pfOutputOnFree N c hc C κ hκ M hbound e) * 2) ^ 2 + 1

def forwardConstant (e : ℝ) : ℝ :=
  (operatorBound (Q := PhysicalCoulombReferenceCore.Reference N c)
    (H := PhysicalFreeForm.EnergyOutput (Index N)) (freeOutputOnPF N c) *
    (PhysicalPFReference.formComparisonConstant (Index N) C κ hκ M hbound e *
      (1 + Real.sqrt 2))) ^ 2 + 1

theorem reverseConstant_pos (e : ℝ) : 0 < reverseConstant N c hc C κ hκ M hbound e := by
  unfold reverseConstant
  positivity

theorem forwardConstant_pos (e : ℝ) : 0 < forwardConstant N c C κ hκ M hbound e := by
  unfold forwardConstant
  positivity

set_option backward.isDefEq.respectTransparency.types true in
theorem pf_energy_le_free (e : ℝ) (u : PhysicalFreeForm.Reference (Index N)) :
    PhysicalPFReference.energy (Index N) (potential N c) C κ hκ M hbound e
      (PhysicalCoulombReferenceCore.referenceEquiv N c hc u) ≤
        reverseConstant N c hc C κ hκ M hbound e * PhysicalFreeForm.energy (Index N) u := by
  have h := operator_sq_of_bound
    (pfOutputOnFree N c hc C κ hκ M hbound e) (PhysicalFreeForm.energyOutput (Index N))
    2 (PhysicalFreeForm.reference_norm_le_energyOutput (Index N)) u
  have hPF := PhysicalPFReference.energyOutput_norm_sq (Index N) (potential N c)
    C κ hκ M hbound e (PhysicalCoulombReferenceCore.referenceEquiv N c hc u)
  have hfree := PhysicalFreeForm.energyOutput_norm_sq (Index N) u
  change ‖PhysicalPFReference.energyOutput (Index N) (potential N c) C κ hκ M hbound e
    (PhysicalCoulombReferenceCore.referenceEquiv N c hc u)‖ ^ 2 ≤ _ at h
  exact hPF.symm.le.trans (h.trans ((mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right zero_le_one) (sq_nonneg _)).trans_eq
      (congrArg (fun t => reverseConstant N c hc C κ hκ M hbound e * t) hfree)))

set_option backward.isDefEq.respectTransparency.types true in
theorem free_energy_le_pf_add_mass (e : ℝ) (u : PhysicalCoulombReferenceCore.Reference N c) :
    PhysicalFreeForm.energy (Index N) (PhysicalCoulombReferenceCore.forget N c u) ≤
      forwardConstant N c C κ hκ M hbound e *
        (PhysicalPFReference.energy (Index N) (potential N c) C κ hκ M hbound e u +
          ‖PhysicalPFReference.inclusion (Index N) (potential N c) u‖ ^ 2) := by
  let K := PhysicalPFReference.formComparisonConstant (Index N) C κ hκ M hbound e *
    (1 + Real.sqrt 2)
  have h := operator_sq_of_bound (freeOutputOnPF N c)
    (PhysicalPFReference.energyGraphMap (Index N) (potential N c) C κ hκ M hbound e)
    K (PhysicalPFReference.reference_norm_le_energyGraph (Index N) (potential N c)
      C κ hκ M hbound e) u
  have hpair := pair_norm_sq_le
    (PhysicalPFReference.inclusion (Index N) (potential N c) u)
    (PhysicalPFReference.energyOutput (Index N) (potential N c) C κ hκ M hbound e u)
  have h' := h.trans (mul_le_mul_of_nonneg_left hpair (sq_nonneg _))
  have hfree := PhysicalFreeForm.energyOutput_norm_sq (Index N)
    (PhysicalCoulombReferenceCore.forget N c u)
  have hPF := PhysicalPFReference.energyOutput_norm_sq (Index N) (potential N c)
    C κ hκ M hbound e u
  change ‖PhysicalFreeForm.energyOutput (Index N)
    (PhysicalCoulombReferenceCore.forget N c u)‖ ^ 2 ≤ _ at h'
  have hcoeff : (operatorBound (Q := PhysicalCoulombReferenceCore.Reference N c)
    (H := PhysicalFreeForm.EnergyOutput (Index N)) (freeOutputOnPF N c) * K) ^ 2 *
      (‖PhysicalPFReference.inclusion (Index N) (potential N c) u‖ ^ 2 +
        ‖PhysicalPFReference.energyOutput (Index N) (potential N c) C κ hκ M hbound e u‖ ^ 2) ≤
      forwardConstant N c C κ hκ M hbound e *
      (‖PhysicalPFReference.inclusion (Index N) (potential N c) u‖ ^ 2 +
        ‖PhysicalPFReference.energyOutput (Index N) (potential N c) C κ hκ M hbound e u‖ ^ 2) :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (add_nonneg (sq_nonneg ‖PhysicalPFReference.inclusion (Index N) (potential N c) u‖)
      (sq_nonneg ‖PhysicalPFReference.energyOutput (Index N) (potential N c) C κ hκ M hbound e u‖))
  have hend := h'.trans hcoeff
  have heq : forwardConstant N c C κ hκ M hbound e *
      (‖PhysicalPFReference.inclusion (Index N) (potential N c) u‖ ^ 2 +
        ‖PhysicalPFReference.energyOutput (Index N) (potential N c) C κ hκ M hbound e u‖ ^ 2) =
      forwardConstant N c C κ hκ M hbound e *
        (PhysicalPFReference.energy (Index N) (potential N c) C κ hκ M hbound e u +
          ‖PhysicalPFReference.inclusion (Index N) (potential N c) u‖ ^ 2) := by
    exact congrArg (fun t => forwardConstant N c C κ hκ M hbound e * t)
      ((congrArg (fun t => ‖PhysicalPFReference.inclusion (Index N) (potential N c) u‖ ^ 2 + t)
        hPF).trans (add_comm _ _))
  exact hfree.symm.le.trans (hend.trans_eq heq)

variable (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

set_option backward.isDefEq.respectTransparency.types true in
theorem normal_pf_rankOne_le_free (e : ℝ) (v : PhysicalFreeForm.WaveSpace (Index N)) :
    (PhysicalPFReference.normalEnergy (Index N) (potential N c) C κ hκ M hbound B S e).expectation
      ((B.realization (PhysicalFreeForm.WaveSpace (Index N))).rank.rankOne v) ≤
        ENNReal.ofReal (reverseConstant N c hc C κ hκ M hbound e) *
          (PhysicalFreeForm.normalEnergy (Index N) B S).expectation
            ((B.realization (PhysicalFreeForm.WaveSpace (Index N))).rank.rankOne v) := by
  let L (v : PhysicalFreeForm.WaveSpace (Index N)) :=
    (PhysicalPFReference.normalEnergy (Index N) (potential N c) C κ hκ M hbound B S e).expectation
      ((B.realization (PhysicalFreeForm.WaveSpace (Index N))).rank.rankOne v)
  let R (v : PhysicalFreeForm.WaveSpace (Index N)) :=
    (PhysicalFreeForm.normalEnergy (Index N) B S).expectation
      ((B.realization (PhysicalFreeForm.WaveSpace (Index N))).rank.rankOne v)
  have hb := reverseConstant_pos N c hc C κ hκ M hbound e
  have h := comparison_from_finite L R (fun _ => 0) (PhysicalFreeForm.inclusion (Index N))
    (ENNReal.ofReal (reverseConstant N c hc C κ hκ M hbound e))
    (ne_of_gt (ENNReal.ofReal_pos.mpr hb))
  have hf : ∀ w, R w < ⊤ → ∃ u, PhysicalFreeForm.inclusion (Index N) u = w := by
    intro w hw
    apply (PhysicalFreeForm.normalEnergy_finite_iff (Index N) B S w).mp
    exact hw
  have hg (u : PhysicalFreeForm.Reference (Index N)) :
      L (PhysicalFreeForm.inclusion (Index N) u) ≤
        ENNReal.ofReal (reverseConstant N c hc C κ hκ M hbound e) *
          (R (PhysicalFreeForm.inclusion (Index N) u) + 0) := by
    have hp := PhysicalPFReference.normalEnergy_rankOne (Index N) (potential N c)
      C κ hκ M hbound B S e (PhysicalCoulombReferenceCore.referenceEquiv N c hc u)
    have he := PhysicalFreeForm.normalEnergy_rankOne (Index N) B S u
    have hr := ENNReal.ofReal_le_ofReal (pf_energy_le_free N c hc C κ hκ M hbound e u)
    exact hp.le.trans (hr.trans_eq ((ENNReal.ofReal_mul hb.le).trans
      (congrArg (fun t => ENNReal.ofReal (reverseConstant N c hc C κ hκ M hbound e) * t)
        (he.symm.trans (add_zero _).symm))))
  exact (h hf hg v).trans_eq (congrArg
    (fun t => ENNReal.ofReal (reverseConstant N c hc C κ hκ M hbound e) * t) (add_zero _))

set_option backward.isDefEq.respectTransparency.types true in
theorem normal_free_rankOne_le_pf_add_mass (e : ℝ) (v : PhysicalFreeForm.WaveSpace (Index N)) :
    (PhysicalFreeForm.normalEnergy (Index N) B S).expectation
      ((B.realization (PhysicalFreeForm.WaveSpace (Index N))).rank.rankOne v) ≤
        ENNReal.ofReal (forwardConstant N c C κ hκ M hbound e) *
          ((PhysicalPFReference.normalEnergy (Index N) (potential N c) C κ hκ M hbound B S e).expectation
            ((B.realization (PhysicalFreeForm.WaveSpace (Index N))).rank.rankOne v) +
              ENNReal.ofReal (‖v‖ ^ 2)) := by
  let L (v : PhysicalFreeForm.WaveSpace (Index N)) :=
    (PhysicalFreeForm.normalEnergy (Index N) B S).expectation
      ((B.realization (PhysicalFreeForm.WaveSpace (Index N))).rank.rankOne v)
  let R (v : PhysicalFreeForm.WaveSpace (Index N)) :=
    (PhysicalPFReference.normalEnergy (Index N) (potential N c) C κ hκ M hbound B S e).expectation
      ((B.realization (PhysicalFreeForm.WaveSpace (Index N))).rank.rankOne v)
  have ha := forwardConstant_pos N c C κ hκ M hbound e
  apply comparison_from_finite L R (fun w => ENNReal.ofReal (‖w‖ ^ 2))
    (PhysicalPFReference.inclusion (Index N) (potential N c))
    (ENNReal.ofReal (forwardConstant N c C κ hκ M hbound e))
    (ne_of_gt (ENNReal.ofReal_pos.mpr ha))
  · intro w hw
    apply (PhysicalPFRadiation.normalEnergy_rankOne_finite_iff
      (Index N) (potential N c) C κ hκ M hbound B S e w).mp
    exact hw
  · intro u
    have hp := PhysicalPFReference.normalEnergy_rankOne (Index N) (potential N c)
      C κ hκ M hbound B S e u
    have he := PhysicalFreeForm.normalEnergy_rankOne (Index N) B S
      (PhysicalCoulombReferenceCore.forget N c u)
    have hr := ENNReal.ofReal_le_ofReal (free_energy_le_pf_add_mass N c C κ hκ M hbound e u)
    have hsum := ENNReal.ofReal_add
      (PhysicalPFReference.energy_nonneg (Index N) (potential N c) C κ hκ M hbound e u)
      (sq_nonneg ‖PhysicalPFReference.inclusion (Index N) (potential N c) u‖)
    exact he.le.trans (hr.trans_eq ((ENNReal.ofReal_mul ha.le).trans
      (congrArg (fun t => ENNReal.ofReal (forwardConstant N c C κ hκ M hbound e) * t)
        (hsum.trans (congrArg (fun t => t +
          ENNReal.ofReal (‖PhysicalPFReference.inclusion (Index N) (potential N c) u‖ ^ 2)) hp.symm)))))

/-- The forward comparison holds for every positive normal trace. -/
theorem normal_free_le_pf_add_mass (e : ℝ)
    {x : B.Trace (PhysicalFreeForm.WaveSpace (Index N))}
    (hx : x ∈ (B.realization (PhysicalFreeForm.WaveSpace (Index N))).rank.positive) :
    (PhysicalFreeForm.normalEnergy (Index N) B S).expectation x ≤
      ENNReal.ofReal (forwardConstant N c C κ hκ M hbound e) *
        ((PhysicalPFReference.normalEnergy (Index N) (potential N c) C κ hκ M hbound B S e).expectation x +
          ENNReal.ofReal ((B.realization (PhysicalFreeForm.WaveSpace (Index N))).rank.trace x)) :=
  PhysicalNormalFormOrder.expectation_le_mul_add_mass_of_rankOne B.normal
    (B.realization (PhysicalFreeForm.WaveSpace (Index N))).functional _ _ _
    (normal_free_rankOne_le_pf_add_mass N c C κ hκ M hbound B S e) hx

/-- The reverse comparison also includes infinite-energy positive traces. -/
theorem normal_pf_le_free (e : ℝ)
    {x : B.Trace (PhysicalFreeForm.WaveSpace (Index N))}
    (hx : x ∈ (B.realization (PhysicalFreeForm.WaveSpace (Index N))).rank.positive) :
    (PhysicalPFReference.normalEnergy (Index N) (potential N c) C κ hκ M hbound B S e).expectation x ≤
      ENNReal.ofReal (reverseConstant N c hc C κ hκ M hbound e) *
        (PhysicalFreeForm.normalEnergy (Index N) B S).expectation x :=
  PhysicalNormalFormOrder.expectation_le_mul_of_rankOne B.normal
    (B.realization (PhysicalFreeForm.WaveSpace (Index N))).functional _ _ _
    (normal_pf_rankOne_le_free N c hc C κ hκ M hbound B S e) hx

end GptLean.PhysicalPFComparison
