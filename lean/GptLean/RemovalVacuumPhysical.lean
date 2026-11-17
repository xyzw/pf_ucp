import GptLean.RemovalVacuumKernels

/-! The physical vacuum correction follows from the same cutoff kernels
used in removal. Only universal tensor-form evaluation and vacuum-sector
orthogonality are operator background. -/

noncomputable section

namespace GptLean.RemovalVacuum

open MeasureTheory Gaussian SymmetricLift RemovalState
open scoped ENNReal

variable {Q Ω Hs K G H Hfull T Tfull : Type*}
  [MeasurableSpace Q] [MeasurableSpace Ω] {μ : Measure Q} {ν : Measure Ω}
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Hfull] [InnerProductSpace ℂ Hfull]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup Tfull] [NormedSpace ℝ Tfull]
  {W : WienerSegalData Q Hs K G μ} {weight : Ω → ℝ}
  {N : ℕ}

theorem VacuumFormData.energy_bound_from_kernels
    (D : KernelFieldData ν W weight)
    (momentum : Ω → FieldSpace) (k b e : ℝ) (base : Fin 3 → Ω → ℂ)
    (label : Fin 3 → FieldSpace → G)
    (hkernel : ∀ i x, D.kernel (label i x) = softDerivativeKernel momentum [] k x (base i))
    (hA : ∀ i, Integrable (fun y => weight y * ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hB : ∀ i, Integrable (fun y => ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hcut : ∀ i, (∫ y, ‖softBase momentum k (base i) y‖ ^ 2 ∂ν) ≤ b ^ 2)
    (Ω₀ : Hs) (hΩ : ‖Ω₀‖ = 1) (hrad : D.radiationDomain Ω₀) (hzero : D.radiation Ω₀ = 0)
    (horth : ∀ i x, inner ℂ Ω₀ (W.field (label i x) Ω₀) = 0)
    (R : RankOneData (Lp H 2 (volume : Measure (Configuration N))) T)
    (Tr : PositiveTraceData T) (E : PositiveForm Tr)
    (Rfull : RankOneData Hfull Tfull) (Trfull : PositiveTraceData Tfull)
    (Efull : PositiveForm Trfull)
    (J : Lp H 2 (volume : Measure (Configuration N)) →ₗᵢ[ℂ] Hfull)
    (forms : VacuumFormData R Tr E Rfull Trfull Efull J Ω₀
      (fun (j : Fin N × Fin 3) x => W.field (label j.2 (particle x j.1)) Ω₀) e) :
    ∀ v, E.expectation (R.rankOne v) < ⊤ →
      Efull.expectation (Rfull.rankOne (J v)) ≤ E.expectation (R.rankOne v) +
        ENNReal.ofReal (((3 * (N : ℝ) / 2) * e ^ 2 * b ^ 2) * ‖v‖ ^ 2) := by
  apply forms.energy_bound hΩ
    (Filter.Eventually.of_forall (fun x j => horth j.2 (particle x j.1)))
    (Filter.Eventually.of_forall (D.many_particle_vacuum_variance N momentum k base label
      hkernel hA hB Ω₀ hΩ hrad hzero))
  exact KernelFieldData.many_particle_vacuum_variance_le N momentum k b base hcut

end GptLean.RemovalVacuum
