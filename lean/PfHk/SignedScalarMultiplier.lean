import PfHk.PhysicalLocalEnergyRough

/-! The positive and negative form amplitudes of a real scalar potential
are defined for every vector on which the scalar operator is defined.
Their squared multiplier difference is the original scalar potential. -/

noncomputable section
namespace PfHk.SignedScalarMultiplier

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PhysicalLocalEnergy

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 30000

attribute [local irreducible] inclusion roughMultiply HasMultiplier

private theorem real_smul_norm_mono {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (a b : ℝ) (v : H) (h : |a| ≤ |b|) : ‖a • v‖ ≤ ‖b • v‖ := by
  simp only [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

private theorem root_smul_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (b : ℝ) (v : H) : ‖Real.sqrt (max b 0) • v‖ ≤ ‖v‖ + ‖b • v‖ := by
  have ha0 := Real.sqrt_nonneg (max b 0)
  have hsquare := Real.sq_sqrt (le_max_right b 0)
  have hmax : max b 0 ≤ |b| := max_le (le_abs_self _) (abs_nonneg _)
  have habs : Real.sqrt (max b 0) ≤ 1 + |b| := by
    nlinarith [abs_nonneg b, sq_nonneg (|b|)]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right habs (norm_nonneg v)).trans_eq (by ring)

private theorem toLp_difference {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {μ : Measure X}
    (u : X → H) (a b c : X → ℝ)
    (ha : MemLp (fun x => a x • u x) 2 μ)
    (hb : MemLp (fun x => b x • u x) 2 μ)
    (hc : MemLp (fun x => c x • u x) 2 μ)
    (heq : ∀ x, a x - b x = c x) :
    ha.toLp _ - hb.toLp _ = hc.toLp _ := by
  rw [← MemLp.toLp_sub]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => by
    change a x • u x - b x • u x = c x • u x
    rw [← sub_smul, heq x]

variable {I : Type} [Fintype I] [DecidableEq I]

def positiveAmplitude (b : Position I → ℝ) (x : Position I) : ℝ :=
  Real.sqrt (max (b x) 0)

def negativeAmplitude (b : Position I → ℝ) (x : Position I) : ℝ :=
  Real.sqrt (max (-b x) 0)

theorem positiveAmplitude_sq (b : Position I → ℝ) (x : Position I) :
    positiveAmplitude b x ^ 2 = max (b x) 0 := Real.sq_sqrt (le_max_right _ _)

theorem negativeAmplitude_sq (b : Position I → ℝ) (x : Position I) :
    negativeAmplitude b x ^ 2 = max (-b x) 0 := Real.sq_sqrt (le_max_right _ _)

theorem amplitude_difference (b : Position I → ℝ) (x : Position I) :
    positiveAmplitude b x ^ 2 - negativeAmplitude b x ^ 2 = b x := by
  rw [positiveAmplitude_sq, negativeAmplitude_sq]
  by_cases h : 0 ≤ b x
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

theorem hasMultiplier_of_abs_le (u : WaveSpace I) {a b : Position I → ℝ}
    (ha : AEStronglyMeasurable a volume) (hb : HasMultiplier b u)
    (hle : ∀ᵐ x ∂volume, |a x| ≤ |b x|) : HasMultiplier a u := by
  unfold HasMultiplier at hb ⊢
  apply hb.mono (ha.smul (Lp.aestronglyMeasurable u))
  filter_upwards [hle] with x hx
  exact real_smul_norm_mono (a x) (b x) (u x) hx

theorem hasMultiplier_positiveAmplitude (u : WaveSpace I) (b : Position I → ℝ)
    (hbmeas : AEStronglyMeasurable b volume) (hb : HasMultiplier b u) :
    HasMultiplier (positiveAmplitude b) u := by
  unfold HasMultiplier at hb ⊢
  have ha : AEStronglyMeasurable (positiveAmplitude b) volume :=
    (Real.continuous_sqrt.comp (continuous_id.max continuous_const)).comp_aestronglyMeasurable
      hbmeas
  have hbound : MemLp (fun x => ‖u x‖ + ‖b x • u x‖) 2 volume :=
    (Lp.memLp u).norm.add hb.norm
  apply hbound.mono' (ha.smul (Lp.aestronglyMeasurable u))
  filter_upwards [] with x
  exact root_smul_bound (b x) (u x)

theorem hasMultiplier_neg (u : WaveSpace I) (b : Position I → ℝ)
    (hb : HasMultiplier b u) : HasMultiplier (fun x => -b x) u := by
  unfold HasMultiplier at hb ⊢
  apply hb.neg.ae_eq
  exact ae_of_all _ fun x => by simp only [Pi.neg_apply, neg_smul]

theorem hasMultiplier_negativeAmplitude (u : WaveSpace I) (b : Position I → ℝ)
    (hbmeas : AEStronglyMeasurable b volume) (hb : HasMultiplier b u) :
    HasMultiplier (negativeAmplitude b) u :=
  hasMultiplier_positiveAmplitude u (fun x => -b x) hbmeas.neg (hasMultiplier_neg u b hb)

theorem hasMultiplier_positiveSquare (u : WaveSpace I) (b : Position I → ℝ)
    (hbmeas : AEStronglyMeasurable b volume) (hb : HasMultiplier b u) :
    HasMultiplier (fun x => positiveAmplitude b x ^ 2) u := by
  apply hasMultiplier_of_abs_le u
    (((Real.continuous_sqrt.comp (continuous_id.max continuous_const)).pow 2).comp_aestronglyMeasurable
      hbmeas) hb
  filter_upwards [] with x
  change |positiveAmplitude b x ^ 2| ≤ |b x|
  rw [positiveAmplitude_sq, abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem hasMultiplier_negativeSquare (u : WaveSpace I) (b : Position I → ℝ)
    (hbmeas : AEStronglyMeasurable b volume) (hb : HasMultiplier b u) :
    HasMultiplier (fun x => negativeAmplitude b x ^ 2) u := by
  apply hasMultiplier_of_abs_le u
    (((Real.continuous_sqrt.comp (continuous_id.max continuous_const)).pow 2).comp_aestronglyMeasurable
      hbmeas.neg) hb
  filter_upwards [] with x
  change |negativeAmplitude b x ^ 2| ≤ |b x|
  rw [negativeAmplitude_sq, abs_of_nonneg (le_max_right _ _)]
  exact max_le (neg_le_abs _) (abs_nonneg _)

theorem operator_difference (u : WaveSpace I) (b : Position I → ℝ)
    (hb : HasMultiplier b u)
    (hp : HasMultiplier (fun x => positiveAmplitude b x ^ 2) u)
    (hn : HasMultiplier (fun x => negativeAmplitude b x ^ 2) u) :
    roughMultiply (fun x => positiveAmplitude b x ^ 2) u hp -
      roughMultiply (fun x => negativeAmplitude b x ^ 2) u hn = roughMultiply b u hb := by
  unfold roughMultiply
  unfold HasMultiplier at hp hn hb
  exact toLp_difference (fun x => u x) (fun x => positiveAmplitude b x ^ 2)
    (fun x => negativeAmplitude b x ^ 2) b hp hn hb (amplitude_difference b)

end PfHk.SignedScalarMultiplier
