import GptLean.RemovalVacuum
import GptLean.RemovalChannel

/-!
Vacuum preparation at the level of the actual spatial form integrals.
The only operator input is the usual hard and tensor-vacuum rank-one
evaluation. The variance calculation then proves the energy bound needed
by the common output-state construction.
-/

noncomputable section

namespace GptLean.RemovalVacuum

open MeasureTheory Filter RemovalState RemovalEnergy
open scoped ENNReal

variable {X I K V Hfull T Tfull : Type*} [MeasurableSpace X] {ν : Measure X}
  [Fintype I]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup Hfull] [InnerProductSpace ℂ Hfull]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup Tfull] [NormedSpace ℝ Tfull]

/-- The standard simple-tensor rank-one form identities, valid for every
hard finite-energy vector. This background contains no removal channel
and no vacuum energy inequality. The variance is not a field here. -/
structure VacuumFormData
    (R : Gaussian.RankOneData (Lp K 2 ν) T) (Tr : PositiveTraceData T) (E : PositiveForm Tr)
    (Rfull : Gaussian.RankOneData Hfull Tfull) (Trfull : PositiveTraceData Tfull)
    (Efull : PositiveForm Trfull) (J : Lp K 2 ν →ₗᵢ[ℂ] Hfull)
    (Ω : V) (χ : I → X → V) (e : ℝ) where
  derivative : Lp K 2 ν → I → X → K
  rest : Lp K 2 ν → ℝ
  kinetic_integrable : ∀ v, E.expectation (R.rankOne v) < ⊤ →
    Integrable (fun x => (1 / 2 : ℝ) * ∑ i, ‖derivative v i x‖ ^ 2) ν
  hard_form : ∀ v, E.expectation (R.rankOne v) < ⊤ →
    E.expectation (R.rankOne v) =
      ENNReal.ofReal ((∫ x, (1 / 2 : ℝ) * ∑ i, ‖derivative v i x‖ ^ 2 ∂ν) + rest v)
  full_form : ∀ v, E.expectation (R.rankOne v) < ⊤ →
    Efull.expectation (Rfull.rankOne (J v)) =
      ENNReal.ofReal ((∫ x, (1 / 2 : ℝ) * ∑ i,
        ‖vacuumDerivative Ω (χ i x) e (derivative v i x) (v x)‖ ^ 2 ∂ν) + rest v)

theorem VacuumFormData.energy_bound
    {R : Gaussian.RankOneData (Lp K 2 ν) T} {Tr : PositiveTraceData T} {E : PositiveForm Tr}
    {Rfull : Gaussian.RankOneData Hfull Tfull} {Trfull : PositiveTraceData Tfull}
    {Efull : PositiveForm Trfull} {J : Lp K 2 ν →ₗᵢ[ℂ] Hfull}
    {Ω : V} {χ : I → X → V} {e σ Cv b : ℝ}
    (D : VacuumFormData R Tr E Rfull Trfull Efull J Ω χ e)
    (hΩ : ‖Ω‖ = 1) (hχ : ∀ᵐ x ∂ν, ∀ i, inner ℂ Ω (χ i x) = 0)
    (hvariance : ∀ᵐ x ∂ν, ∑ i, ‖χ i x‖ ^ 2 = σ)
    (hσ : σ ≤ 2 * Cv * b ^ 2) :
    ∀ v, E.expectation (R.rankOne v) < ⊤ →
      Efull.expectation (Rfull.rankOne (J v)) ≤ E.expectation (R.rankOne v) +
        ENNReal.ofReal ((Cv * e ^ 2 * b ^ 2) * ‖v‖ ^ 2) := by
  intro v hv
  have hp : Integrable (fun x => ‖v x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hn : (∫ x, ‖v x‖ ^ 2 ∂ν) = ‖v‖ ^ 2 := by
    simpa only [Lp.toLp_coeFn] using (Repair.toL2_norm_sq (Lp.memLp v)).symm
  have heq := (integrated_vacuum_kinetic_eq Ω χ hΩ hχ e σ hvariance
    (D.derivative v) v (D.kinetic_integrable v hv) hp).2
  rw [D.full_form v hv, heq, hn, D.hard_form v hv]
  have hcost : (e ^ 2 / 2 * σ) * ‖v‖ ^ 2 ≤ (Cv * e ^ 2 * b ^ 2) * ‖v‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hσ (sq_nonneg e)]
  rw [add_right_comm]
  exact ENNReal.ofReal_add_le.trans
    (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hcost))

/-- The corresponding tested current identity follows from the same
vacuum derivative, including spatially varying vacuum fields. -/
theorem vacuum_current_of_formulas
    (Ω : V) (χ : X → V) (hΩ : ‖Ω‖ = 1)
    (hχ : ∀ᵐ x ∂ν, inner ℂ Ω (χ x) = 0)
    (e : ℝ) (ψ u : X → K) (weight : X → ℝ)
    (hard full : ℝ)
    (hhard : hard = ∫ x, weight x * (inner ℂ (ψ x) (u x)).re ∂ν)
    (hfull : full = ∫ x, weight x *
      (inner ℂ (vacuumEmbedding Ω hΩ (ψ x)) (vacuumDerivative Ω (χ x) e (u x) (ψ x))).re ∂ν) :
    full = hard := by
  rw [hhard, hfull]
  exact integral_congr_ae (hχ.mono (fun x hx => by
    dsimp only
    rw [vacuumDerivative_inner Ω (χ x) hΩ hx]))

end GptLean.RemovalVacuum
