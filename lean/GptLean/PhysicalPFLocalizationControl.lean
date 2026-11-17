import GptLean.PhysicalPFTestControl
import GptLean.PhysicalPFEnergyTruncation

/-!
The localization control is the constructed Pauli–Fierz energy with trace
mass added. Its comparison with energy, mass, and the physical component
forms is proved on the whole positive cone, including infinite energies.
-/

noncomputable section

namespace GptLean.PhysicalPFLocalization

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalPFSource RemovalState
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

private theorem mass_le_of_control_eq (r s : ℝ≥0∞) (a : ℝ)
    (h : r = ENNReal.ofReal (s.toReal + a)) : ENNReal.ofReal a ≤ r :=
  (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left ENNReal.toReal_nonneg)).trans_eq h.symm

private theorem sqrt_bound_of_square {a : ℝ} (ha : 0 ≤ a) {r : ℝ≥0∞}
    (hr : r < ⊤) (h : ENNReal.ofReal (a ^ 2) ≤ r) : a ≤ Real.sqrt r.toReal := by
  apply (Real.le_sqrt ha ENNReal.toReal_nonneg).mpr
  exact (ENNReal.toReal_ofReal (sq_nonneg a)).symm.le.trans
    (ENNReal.toReal_mono hr.ne h)

private theorem sqrt_bound_of_control_eq (a b : ℝ) (ha : 0 ≤ a)
    (hab : a ^ 2 ≤ b) (r : ℝ≥0∞) (hr : r = ENNReal.ofReal b) :
    a ≤ Real.sqrt r.toReal := by
  have hb : 0 ≤ b := (sq_nonneg a).trans hab
  have he : r.toReal = b := (congrArg ENNReal.toReal hr).trans (ENNReal.toReal_ofReal hb)
  exact (Real.le_sqrt ha ENNReal.toReal_nonneg).mpr (hab.trans_eq he.symm)

private theorem sum_le_scaled_card {α : Type*} [Fintype α]
    (f : α → ℝ) (c d : ℝ) (h : ∀ i, f i ≤ c * d) :
    (∑ i, f i) ≤ ((Fintype.card α : ℝ) * c) * d := by
  calc
    (∑ i, f i) ≤ ∑ _i : α, c * d := Finset.sum_le_sum fun i _ => h i
    _ = ((Fintype.card α : ℝ) * c) * d := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

private theorem add_le_twice {a b c : ℝ} (ha : a ≤ c) (hb : b ≤ c) :
    a + b ≤ 2 * c := by linarith

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

theorem energy_le_control {x : B.Trace (WaveSpace I)}
    (hx : x ∈ (B.realization (WaveSpace I)).rank.positive) :
    (normalEnergy I V C κ hκ M hbound B S e).expectation x ≤
      (currentControl I V C κ hκ M hbound B S e).expectation x := by
  by_cases hc : (currentControl I V C κ hκ M hbound B S e).expectation x < ⊤
  · have he := (currentControl_finite_iff I V C κ hκ M hbound B S e hx).mp hc
    rw [currentControl_expectation I V C κ hκ M hbound B S e hx he]
    conv_lhs => rw [← ENNReal.ofReal_toReal he.ne]
    apply ENNReal.ofReal_le_ofReal
    have ht : 0 ≤ (B.realization (WaveSpace I)).rank.trace x := by
      exact (norm_nonneg x).trans_eq ((B.traceData (H := WaveSpace I)).norm_eq_trace hx)
    exact le_add_of_nonneg_right ht
  · exact le_top.trans_eq (top_unique (not_lt.mp hc)).symm

theorem mass_le_control {x : B.Trace (WaveSpace I)}
    (hx : x ∈ (B.realization (WaveSpace I)).rank.positive) :
    ENNReal.ofReal ((B.realization (WaveSpace I)).rank.trace x) ≤
      (currentControl I V C κ hκ M hbound B S e).expectation x := by
  by_cases hc : (currentControl I V C κ hκ M hbound B S e).expectation x < ⊤
  · have he := (currentControl_finite_iff I V C κ hκ M hbound B S e hx).mp hc
    exact mass_le_of_control_eq _ _ _
      (currentControl_expectation I V C κ hκ M hbound B S e hx he)
  · exact le_top.trans_eq (top_unique (not_lt.mp hc)).symm

theorem control_rankOne (u : Reference I V) :
    (currentControl I V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne (inclusion I V u)) =
        ENNReal.ofReal (energy I V C κ hκ M hbound e u + ‖inclusion I V u‖ ^ 2) := by
  have he := normalEnergy_rankOne I V C κ hκ M hbound B S e u
  have hf : (normalEnergy I V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne (inclusion I V u)) < ⊤ :=
    he.le.trans_lt ENNReal.ofReal_lt_top
  have h := currentControl_expectation I V C κ hκ M hbound B S e
    ((B.realization (WaveSpace I)).rank.rankOne_positive _) hf
  have hreal := (congrArg ENNReal.toReal he).trans
    (ENNReal.toReal_ofReal (energy_nonneg I V C κ hκ M hbound e u))
  have hmass := (B.realization (WaveSpace I)).rank.trace_rankOne (inclusion I V u)
  exact h.trans (congrArg ENNReal.ofReal (congrArg₂ (fun a b : ℝ => a + b) hreal hmass))

theorem control_rankOne_finite (u : Reference I V) :
    (currentControl I V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne (inclusion I V u)) < ⊤ :=
  (control_rankOne I V C κ hκ M hbound B S e u).le.trans_lt ENNReal.ofReal_lt_top

theorem norm_le_sqrt_control (v : WaveSpace I)
    (hv : (currentControl I V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne v) < ⊤) :
    ‖v‖ ≤ Real.sqrt ((currentControl I V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne v)).toReal := by
  have hm := mass_le_control I V C κ hκ M hbound B S e
    ((B.realization (WaveSpace I)).rank.rankOne_positive v)
  have hs := (congrArg ENNReal.ofReal
    ((B.realization (WaveSpace I)).rank.trace_rankOne v)).symm.le.trans hm
  exact sqrt_bound_of_square (norm_nonneg v) hv hs

theorem radiation_norm_le_sqrt_control (u : Reference I V) :
    ‖radiation I V u‖ ≤ Real.sqrt
      ((currentControl I V C κ hκ M hbound B S e).expectation
        ((B.realization (WaveSpace I)).rank.rankOne (inclusion I V u))).toReal := by
  exact sqrt_bound_of_control_eq _ _ (norm_nonneg (radiation I V u))
    ((PhysicalPFReference.radiation_le_energy I V C κ hκ M hbound e u).trans
      (le_add_of_nonneg_right (sq_nonneg (‖inclusion I V u‖)))) _
    (control_rankOne I V C κ hκ M hbound B S e u)

theorem radiationSource_norm_le_control (u : Reference I V) :
    ‖radiationSource I V u‖ ≤ 2 * Real.sqrt
      ((currentControl I V C κ hκ M hbound B S e).expectation
        ((B.realization (WaveSpace I)).rank.rankOne (inclusion I V u))).toReal := by
  have hm := norm_le_sqrt_control I V C κ hκ M hbound B S e (inclusion I V u)
    (control_rankOne_finite I V C κ hκ M hbound B S e u)
  have hr := radiation_norm_le_sqrt_control I V C κ hκ M hbound B S e u
  exact (radiationSource_norm_le I V u).trans (add_le_twice hm hr)

theorem energyOutput_norm_le_sqrt_control (u : Reference I V) :
    ‖energyOutput I V C κ hκ M hbound e u‖ ≤ Real.sqrt
      ((currentControl I V C κ hκ M hbound B S e).expectation
        ((B.realization (WaveSpace I)).rank.rankOne (inclusion I V u))).toReal := by
  exact sqrt_bound_of_control_eq _ _
    (norm_nonneg (energyOutput I V C κ hκ M hbound e u))
    ((energyOutput_norm_sq I V C κ hκ M hbound e u).le.trans
      (le_add_of_nonneg_right (sq_nonneg (‖inclusion I V u‖)))) _
    (control_rankOne I V C κ hκ M hbound B S e u)

theorem covariant_sum_le_control (u : Reference I V) :
    (∑ i, ‖covariant I V C κ hκ M hbound e i u‖) ≤
      ((Fintype.card I : ℝ) * Real.sqrt 2) * Real.sqrt
        ((currentControl I V C κ hκ M hbound B S e).expectation
          ((B.realization (WaveSpace I)).rank.rankOne (inclusion I V u))).toReal := by
  have h (i : I) := (covariant_norm_le_energyOutput I V C κ hκ M hbound e i u).trans
    (mul_le_mul_of_nonneg_left (energyOutput_norm_le_sqrt_control I V C κ hκ M hbound B S e u)
      (Real.sqrt_nonneg 2))
  exact sum_le_scaled_card _ _ _ h

section Components

variable (N : ℕ)
  (κN : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκN : ∀ i, AEStronglyMeasurable (κN i) volume)
  (hboundN : ∀ i, ∀ᵐ x ∂volume, ‖κN i x‖ ≤ M)

theorem kinetic_le_control {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (hx : x ∈ (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive) :
    (PhysicalPFDecomposition.kinetic N B S C κN hκN M hboundN e).expectation x ≤
      (currentControl (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
        C κN hκN M hboundN B S e).expectation x :=
  (PhysicalPFEnergyTruncation.kinetic_le_energy N B S C κN hκN M hboundN e hx).trans
    (energy_le_control (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C κN hκN M hboundN B S e hx)

theorem coulomb_le_control {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (hx : x ∈ (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive) :
    (PhysicalPFDecomposition.coulomb N B).expectation x ≤
      (currentControl (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
        C κN hκN M hboundN B S e).expectation x :=
  (PhysicalPFEnergyTruncation.coulomb_le_energy N B S C κN hκN M hboundN e hx).trans
    (energy_le_control (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C κN hκN M hboundN B S e hx)

theorem radiation_le_control {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (hx : x ∈ (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive) :
    (PhysicalPFDecomposition.radiation N B).expectation x ≤
      (currentControl (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
        C κN hκN M hboundN B S e).expectation x :=
  (PhysicalPFEnergyTruncation.radiation_le_energy N B S C κN hκN M hboundN e hx).trans
    (energy_le_control (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C κN hκN M hboundN B S e hx)

end Components

end GptLean.PhysicalPFLocalization
