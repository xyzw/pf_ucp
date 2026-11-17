import GptLean.PhysicalGroundStateAmplitude

/-!
The common-ground-state argument in `pf_ucp.tex` on the actual physical
Pauli–Fierz model from `gpt_lean`. The state space contains normalized
fermionic form-domain vectors, and its `Pair` consists of the density and
combined current in their physical Lebesgue spaces.

The arguments below add no analytic backgrounds. They retain the existing
CCR, normal trace, and closed form parameters. Photon variations additionally
retain the existing concrete Weyl law.
-/

noncomputable section

namespace PfHk

open MeasureTheory Filter GptLean GptLean.PhysicalPairSpace
  GptLean.PhysicalPairDuality GptLean.PhysicalGroundState
  GptLean.TransformationsGauge GptLean.PhysicalFock
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {N : ℕ} (i : Fin N) (F : PhysicalPolarization.Frame)
  (χ : PhysicalPolarization.ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)
  (B : PhysicalNormalTrace.StandardNormalTraceBackground)
  (S : PhysicalClosedForms.StandardClosedFormBackground) (e : ℝ)

/-- `prop-common-ground-state`. Equality of both observables makes each of
two ground states a ground state of the other Hamiltonian. The real energy
difference is the difference of the potential pairings with the common pair.
This proof allows every real coupling and degenerate ground states. -/
theorem common_ground_state
    {a₁ a₂ : Potential} {p₁ p₂ : State F χ C B S e (N := N)}
    (h₁ : IsGroundState i F χ C B S e a₁ p₁)
    (h₂ : IsGroundState i F χ C B S e a₂ p₂)
    (hd : (model i F χ C B S e).density p₁ =
      (model i F χ C B S e).density p₂) :
    IsGroundState i F χ C B S e a₁ p₂ ∧
      IsGroundState i F χ C B S e a₂ p₁ ∧
      shiftedEnergy i F χ C B S e a₁ p₁ -
          shiftedEnergy i F χ C B S e a₂ p₂ =
        pairPotential a₁ ((model i F χ C B S e).density p₁) -
          pairPotential a₂ ((model i F χ C B S e).density p₁) := by
  have hv₁ := h₁ p₂
  have hv₂ := h₂ p₁
  have he : (model i F χ C B S e).energy p₁ =
      (model i F χ C B S e).energy p₂ := by
    unfold shiftedEnergy at hv₁ hv₂
    rw [← hd] at hv₁ hv₂
    linarith
  have hs (a : Potential) : shiftedEnergy i F χ C B S e a p₁ =
      shiftedEnergy i F χ C B S e a p₂ := by
    unfold shiftedEnergy
    rw [hd, he]
  refine ⟨?_, ?_, ?_⟩
  · intro q
    exact (hs a₁).symm.trans_le (h₁ q)
  · intro q
    exact (hs a₂).trans_le (h₂ q)
  · unfold shiftedEnergy
    rw [← hd, he]
    ring

/-- The potential-pairing difference written as the two integrals in
the energy-difference identity of `prop-common-ground-state`. Here
`a.1` is `v + |A|² / 2`. -/
theorem potential_difference_integrals (a₁ a₂ : Potential) (d : Pair) :
    pairPotential a₁ d - pairPotential a₂ d =
      (∫ x, (a₁.1.val x - a₂.1.val x) * densityL1 d x) +
        ∫ x, inner ℝ (a₁.2.val x - a₂.2.val x) (currentL1 d x) := by
  have hs (a : Potential) : Integrable (fun x => a.1.val x * densityL1 d x) volume := by
    change Integrable (fun x => a.1.val x * fst d.1 x) volume
    simpa only [Real.inner_apply] using (integrable_pairing (p := 3) a.1 d.1)
  have hv (a : Potential) : Integrable
      (fun x => inner ℝ (a.2.val x) (currentL1 d x)) volume :=
    integrable_pairing (p := 3 / 2) a.2 d.2
  simp only [pairPotential_eq_integral, sub_mul, inner_sub_left,
    integral_sub (hs a₁) (hs a₂), integral_sub (hv a₁) (hv a₂)]
  ring

/-- The density-weighted vector-potential difference in `prop-cutoff-kernel`.
Shifted scalar potentials do not enter this expression. -/
def vectorDifference (a₁ a₂ : Potential) (d : Pair) (x : Position) : Vector :=
  densityL1 d x • (a₁.2.val x - a₂.2.val x)

theorem vectorDifference_eq_current_sub (a₁ a₂ : Potential) (d : Pair) (x : Position) :
    vectorDifference a₁ a₂ d x = physicalCurrent a₁ d x - physicalCurrent a₂ d x := by
  simp only [vectorDifference, physicalCurrent, smul_sub]
  abel

theorem vectorDifference_integrable (a₁ a₂ : Potential) (d : Pair) :
    Integrable (vectorDifference a₁ a₂ d) volume := by
  exact ((physicalCurrent_integrable a₁ d).sub (physicalCurrent_integrable a₂ d)).congr
    (ae_of_all _ fun x => (vectorDifference_eq_current_sub a₁ a₂ d x).symm)

/-- The divergence half of `prop-cutoff-kernel`, for every differentiable
test with bounded gradient, hence in particular for every smooth compactly
supported test. No positive coupling assumption is needed for this half. -/
theorem vectorDifference_divergence
    {a₁ a₂ : Potential} {p₁ p₂ : State F χ C B S e (N := N)}
    (h₁ : IsGroundState i F χ C B S e a₁ p₁)
    (h₂ : IsGroundState i F χ C B S e a₂ p₂)
    (hd : (model i F χ C B S e).density p₁ =
      (model i F χ C B S e).density p₂)
    (g : SpatialGauge) :
    ∫ x, inner ℝ (g.gradientVector x)
      (vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁) x) = 0 := by
  have hcommon := (common_ground_state i F χ C B S e h₁ h₂ hd).2.1
  have hg₁ := ground_gauge_zero i F χ C B S e h₁ g
  have hg₂ := ground_gauge_zero i F χ C B S e hcommon g
  have hp : pairPotential a₁
      (g.shiftPair ((model i F χ C B S e).density p₁) -
        (model i F χ C B S e).density p₁) =
      pairPotential a₂
        (g.shiftPair ((model i F χ C B S e).density p₁) -
          (model i F χ C B S e).density p₁) := by linarith
  rw [pairPotential_shift, pairPotential_shift] at hp
  have hint (a : Potential) : Integrable (fun x =>
      inner ℝ (a.2.val x)
        (densityL1 ((model i F χ C B S e).density p₁) x • g.gradientVector x)) volume := by
    have hρA := integrable_density_smul a ((model i F χ C B S e).density p₁)
    refine (hρA.norm.const_mul g.vectorBound).mono'
      (a.2.val.aestronglyMeasurable.inner
        ((Lp.aestronglyMeasurable (densityL1 ((model i F χ C B S e).density p₁))).smul
          g.gradientVector_measurable.aestronglyMeasurable)) ?_
    refine ae_of_all _ fun x => ?_
    rw [inner_smul_right, ← real_inner_smul_left]
    exact (norm_inner_le_norm _ _).trans (by
      nlinarith [g.norm_gradientVector_le x,
        norm_nonneg (densityL1 ((model i F χ C B S e).density p₁) x • a.2.val x)])
  have hid : (∫ x, inner ℝ (g.gradientVector x)
        (vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁) x)) =
      (∫ x, inner ℝ (a₁.2.val x)
        (densityL1 ((model i F χ C B S e).density p₁) x • g.gradientVector x)) -
      ∫ x, inner ℝ (a₂.2.val x)
        (densityL1 ((model i F χ C B S e).density p₁) x • g.gradientVector x) := by
    rw [← integral_sub (hint a₁) (hint a₂)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp only [vectorDifference, inner_smul_right, inner_sub_right]
      rw [real_inner_comm (g.gradientVector x) (a₁.2.val x),
        real_inner_comm (g.gradientVector x) (a₂.2.val x)]
      ring
  rw [hid, hp, sub_self]

end PfHk
