import GptLean.TransformationsGaugeH1
import GptLean.PhysicalPFScalarMultiplier

/-!
The gauge transformation on the actual common Pauli--Fierz reference domain.

The phase `exp (i G) = cos G + i sin G` is the sum of two bounded
differentiable scalar multipliers. The constructed scalar multipliers act on
all three graph coordinates of the reference domain, the electronic H1 graph,
the spatial radiation graph and the Coulomb multiplication graph, and commute
with the spatial field. Hence `U_G` maps the reference domain into itself,
with inverse the phase of `-G`, and the covariant derivatives obey

`Dᵢ (U_G u) = U_G (Dᵢ u + (∂ᵢ G) u)`.

The energy changes by the exact cross and quadratic terms of `energy-gauge`.
These are the domain and energy statements of `prop-gauge-covariance` for
gauge functions with bounded gradient.
-/

noncomputable section

namespace GptLean.TransformationsGauge

open MeasureTheory PhysicalFock PhysicalPFReference TransformationsPhase
  ElectronicH1Multiplier PhysicalPFScalarMultiplier
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

namespace GaugeFunction

variable {I : Type} [Fintype I] [DecidableEq I] (G : GaugeFunction I)
  (V : Position I → ℝ)

/-- The phase on the physical wave space. -/
abbrev wavePhase : WaveSpace I ≃ₗᵢ[ℂ] WaveSpace I := G.phaseL2 (H := PhotonFock)

/-- The gauge transformation `U_G` on the common reference domain. -/
def gaugeReference (u : Reference I V) : Reference I V :=
  multiply V G.cosMultiplier u + Complex.I • multiply V G.sinMultiplier u

/-- A continuous linear observable of the reference domain that turns both
real multipliers into the corresponding L² multipliers sees the phase. -/
private theorem apply_gaugeReference (L : Reference I V →L[ℂ] WaveSpace I) (u : Reference I V)
    (w : WaveSpace I)
    (hc : L (multiply V G.cosMultiplier u) = G.cosMultiplier.multiplier w)
    (hs : L (multiply V G.sinMultiplier u) = G.sinMultiplier.multiplier w) :
    L (G.gaugeReference V u) = G.wavePhase w :=
  ((map_add L (multiply V G.cosMultiplier u) (Complex.I • multiply V G.sinMultiplier u)).trans
    (congrArg₂ (· + ·) hc ((map_smul L Complex.I (multiply V G.sinMultiplier u)).trans
      (congrArg (fun z : WaveSpace I => Complex.I • z) hs)))).trans
    (G.phaseL2_eq_cos_sin (H := PhotonFock) w).symm

theorem inclusion_gaugeReference (u : Reference I V) :
    inclusion I V (G.gaugeReference V u) = G.wavePhase (inclusion I V u) :=
  G.apply_gaugeReference V (inclusion I V) u (inclusion I V u)
    (value_multiply V G.cosMultiplier u) (value_multiply V G.sinMultiplier u)

theorem ordinary_gaugeReference (i : I) (u : Reference I V) :
    ordinary I V i (G.gaugeReference V u) =
      G.wavePhase (ordinary I V i u + Complex.I • G.gradientMultiplier i (inclusion I V u)) :=
  ((map_add (ordinary I V i) (multiply V G.cosMultiplier u)
      (Complex.I • multiply V G.sinMultiplier u)).trans
    (congrArg₂ (· + ·) (ordinary_multiply V G.cosMultiplier u i)
      ((map_smul (ordinary I V i) Complex.I (multiply V G.sinMultiplier u)).trans
        (congrArg (fun z : WaveSpace I => Complex.I • z)
          (ordinary_multiply V G.sinMultiplier u i))))).trans
    (G.gauge_derivative_eq (H := PhotonFock) (electronic I V u) i).symm

theorem radiation_gaugeReference (u : Reference I V) :
    radiation I V (G.gaugeReference V u) = G.wavePhase (radiation I V u) :=
  G.apply_gaugeReference V (radiation I V) u (radiation I V u)
    (radiation_multiply V G.cosMultiplier u) (radiation_multiply V G.sinMultiplier u)

theorem potential_gaugeReference (u : Reference I V) :
    potential I V (G.gaugeReference V u) = G.wavePhase (potential I V u) :=
  G.apply_gaugeReference V (potential I V) u (potential I V u)
    (potential_multiply V G.cosMultiplier u) (potential_multiply V G.sinMultiplier u)

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)

/-- The phase commutes with the actual spatial field `A(xᵢ)`. -/
theorem field_gaugeReference (i : I) (u : Reference I V) :
    field I V C κ hκ M hbound i (G.gaugeReference V u) =
      G.wavePhase (field I V C κ hκ M hbound i u) :=
  G.apply_gaugeReference V (field I V C κ hκ M hbound i) u (field I V C κ hκ M hbound i u)
    (field_multiply V G.cosMultiplier C κ hκ M hbound u i)
    (field_multiply V G.sinMultiplier C κ hκ M hbound u i)

attribute [irreducible] gaugeReference

private theorem covariant_algebra {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E ≃ₗᵢ[ℂ] E) (d g f : E) (e : ℂ) :
    (-Complex.I) • L (d + Complex.I • g) - e • L f = L ((-Complex.I) • d - e • f + g) := by
  simp only [map_add, map_sub, map_smul, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
    one_smul]
  abel

/-- The gauge law of the covariant derivative,
`Dᵢ (U_G u) = U_G (Dᵢ u + (∂ᵢ G) u)`. -/
theorem covariant_gaugeReference (e : ℝ) (i : I) (u : Reference I V) :
    covariant I V C κ hκ M hbound e i (G.gaugeReference V u) =
      G.wavePhase (covariant I V C κ hκ M hbound e i u +
        G.gradientMultiplier i (inclusion I V u)) :=
  (covariant_apply I V C κ hκ M hbound e i (G.gaugeReference V u)).trans
    ((congrArg₂ (fun a b : WaveSpace I => (-Complex.I) • a - (e : ℂ) • b)
      (G.ordinary_gaugeReference V i u) (G.field_gaugeReference V C κ hκ M hbound i u)).trans
      ((covariant_algebra G.wavePhase (ordinary I V i u)
        (G.gradientMultiplier i (inclusion I V u)) (field I V C κ hκ M hbound i u) (e : ℂ)).trans
        (congrArg (fun z : WaveSpace I => G.wavePhase (z + G.gradientMultiplier i (inclusion I V u)))
          (covariant_apply I V C κ hκ M hbound e i u).symm)))

private theorem norm_add_sq_re (a b : WaveSpace I) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * (⟪a, b⟫_ℂ).re + ‖b‖ ^ 2 := by
  simpa only [RCLike.re_to_complex] using norm_add_sq (𝕜 := ℂ) a b

theorem covariant_norm_sq_gaugeReference (e : ℝ) (i : I) (u : Reference I V) :
    ‖covariant I V C κ hκ M hbound e i (G.gaugeReference V u)‖ ^ 2 =
      ‖covariant I V C κ hκ M hbound e i u‖ ^ 2 +
        2 * (⟪covariant I V C κ hκ M hbound e i u,
          G.gradientMultiplier i (inclusion I V u)⟫_ℂ).re +
        ‖G.gradientMultiplier i (inclusion I V u)‖ ^ 2 :=
  (congrArg (fun w : WaveSpace I => ‖w‖ ^ 2)
    (G.covariant_gaugeReference V C κ hκ M hbound e i u)).trans
    ((congrArg (fun t : ℝ => t ^ 2) (G.wavePhase.norm_map _)).trans (norm_add_sq_re _ _))

/-- The covariant kinetic energy after the gauge transformation. -/
theorem kineticEnergy_gaugeReference (e : ℝ) (u : Reference I V) :
    kineticEnergy I V C κ hκ M hbound e (G.gaugeReference V u) =
      kineticEnergy I V C κ hκ M hbound e u +
        ∑ i, (⟪covariant I V C κ hκ M hbound e i u,
          G.gradientMultiplier i (inclusion I V u)⟫_ℂ).re +
        (1 / 2 : ℝ) * ∑ i, ‖G.gradientMultiplier i (inclusion I V u)‖ ^ 2 := by
  unfold kineticEnergy
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl
    fun i (_ : i ∈ Finset.univ) => G.covariant_norm_sq_gaugeReference V C κ hκ M hbound e i u
  refine (congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) h).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The exact internal-energy identity `energy-gauge` on the reference domain:
the cross term and the quadratic gradient term are added, while the
radiation and Coulomb energies are unchanged. -/
theorem energy_gaugeReference (e : ℝ) (u : Reference I V) :
    energy I V C κ hκ M hbound e (G.gaugeReference V u) =
      energy I V C κ hκ M hbound e u +
        ∑ i, (⟪covariant I V C κ hκ M hbound e i u,
          G.gradientMultiplier i (inclusion I V u)⟫_ℂ).re +
        (1 / 2 : ℝ) * ∑ i, ‖G.gradientMultiplier i (inclusion I V u)‖ ^ 2 := by
  have hr : ‖radiation I V (G.gaugeReference V u)‖ = ‖radiation I V u‖ :=
    (congrArg norm (G.radiation_gaugeReference V u)).trans (G.wavePhase.norm_map _)
  have hp : ‖potential I V (G.gaugeReference V u)‖ = ‖potential I V u‖ :=
    (congrArg norm (G.potential_gaugeReference V u)).trans (G.wavePhase.norm_map _)
  unfold energy
  refine (congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (G.kineticEnergy_gaugeReference V C κ hκ M hbound e u) (congrArg (· ^ 2) hr))
    (congrArg (· ^ 2) hp)).trans ?_
  ring

/-- The phase of `-G` inverts the gauge transformation on the reference domain. -/
theorem gaugeReference_neg (u : Reference I V) :
    G.neg.gaugeReference V (G.gaugeReference V u) = u :=
  inclusion_injective I V ((G.neg.inclusion_gaugeReference V (G.gaugeReference V u)).trans
    ((congrArg G.neg.wavePhase (G.inclusion_gaugeReference V u)).trans
      (G.phaseL2_neg (H := PhotonFock) (inclusion I V u))))

theorem gaugeReference_neg_left (u : Reference I V) :
    G.gaugeReference V (G.neg.gaugeReference V u) = u :=
  inclusion_injective I V ((G.inclusion_gaugeReference V (G.neg.gaugeReference V u)).trans
    ((congrArg G.wavePhase (G.neg.inclusion_gaugeReference V u)).trans
      (congrArg ElectronicH1Complex.value (G.gaugeH1_neg_left (H := PhotonFock)
        (electronic I V u)))))

end GaugeFunction

end GptLean.TransformationsGauge
