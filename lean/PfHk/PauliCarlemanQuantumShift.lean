import PfHk.PauliCarlemanQuantum

/-! The quantum Zeeman perturbation together with an arbitrary real
energy shift. Its weighted source is derived from the actual quantum
bound and the mass term of the orbital Carleman estimate. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliCarlemanQuantumShift

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput
  PfHk.PhysicalDyadicEnergy PfHk.SmoothCutoffBounds PfHk.PauliSpin

attribute [local instance] PhysicalLocalExternalCarleman.endpointPhotonRealInner

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

private theorem real_smul_norm_sq {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (E : ℝ) (v : H) : ‖(E : ℂ) • v‖ ^ 2 = E ^ 2 * ‖v‖ ^ 2 := by
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

private theorem finite_shift_bound {X S H : Type*} [MeasurableSpace X] [Fintype S]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (μ : Measure X)
    (w : X → ℝ) (q v g : S → X → H) (E : ℝ)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hoperator : ∀ s, g s =ᵐ[μ] fun x => q s x - (E : ℂ) • v s x)
    (hmeas : AEStronglyMeasurable (fun x => ∑ s, w x * ‖g s x‖ ^ 2) μ)
    (hq : Integrable (fun x => ∑ s, w x * ‖q s x‖ ^ 2) μ)
    (hv : Integrable (fun x => ∑ s, w x * ‖v s x‖ ^ 2) μ) :
    Integrable (fun x => ∑ s, w x * ‖g s x‖ ^ 2) μ ∧
      (∫ x, ∑ s, w x * ‖g s x‖ ^ 2 ∂μ) ≤
        2 * (∫ x, ∑ s, w x * ‖q s x‖ ^ 2 ∂μ) +
          2 * E ^ 2 * ∫ x, ∑ s, w x * ‖v s x‖ ^ 2 ∂μ := by
  let Q := fun x => ∑ s, w x * ‖q s x‖ ^ 2
  let V := fun x => ∑ s, w x * ‖v s x‖ ^ 2
  let G := fun x => ∑ s, w x * ‖g s x‖ ^ 2
  have hbound : ∀ᵐ x ∂μ, G x ≤ 2 * Q x + (2 * E ^ 2) * V x := by
    filter_upwards [hw, ae_all_iff.mpr hoperator] with x hx hrep
    have hs := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
      mul_le_mul_of_nonneg_left (WeightedNorm.sub_sq_bound (q s x) ((E : ℂ) • v s x)) hx
    simpa only [G, Q, V, hrep, real_smul_norm_sq, mul_add, mul_assoc,
      mul_left_comm (w x) 2, mul_left_comm (w x) (E ^ 2), Finset.mul_sum,
      Finset.sum_add_distrib] using hs
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ G x :=
    hw.mono fun x hx => Finset.sum_nonneg fun s _ => mul_nonneg hx (sq_nonneg _)
  have hmajor : Integrable (fun x => 2 * Q x + (2 * E ^ 2) * V x) μ :=
    (hq.const_mul 2).add (hv.const_mul (2 * E ^ 2))
  have hi : Integrable G μ := hmajor.mono' hmeas (by
    filter_upwards [hbound, hnonneg] with x hxb hx0
    exact (Real.norm_of_nonneg hx0).le.trans hxb)
  refine ⟨hi, (integral_mono_ae hi hmajor hbound).trans_eq ?_⟩
  rw [integral_add (hq.const_mul 2) (hv.const_mul (2 * E ^ 2)), integral_const_mul,
    integral_const_mul]

private theorem shift_arithmetic {Q M F a b t s σ E : ℝ}
    (hq : Q ≤ (a * t + b * s) * F) (hm : M ≤ (520 * σ * s) * F) :
    2 * Q + 2 * E ^ 2 * M ≤
      ((2 * a) * t + (2 * b + 1040 * E ^ 2 * σ) * s) * F := by
  calc
    _ ≤ 2 * ((a * t + b * s) * F) + 2 * E ^ 2 * ((520 * σ * s) * F) :=
      add_le_add (mul_le_mul_of_nonneg_left hq (by norm_num))
        (mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) (sq_nonneg _)))
    _ = _ := by ring

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion PauliMagneticOperator.quantum

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

def shifted (hUV : CarlemanUV χ) (E : ℝ) (u : PauliReference.Ref N) (s : SpinIndex N) :
    WaveSpace (Fin N × Fin 3) :=
  PauliMagneticOperator.quantum F χ hUV C e u s -
    (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s)

theorem shifted_ae (hUV : CarlemanUV χ) (E : ℝ) (u : PauliReference.Ref N) (s : SpinIndex N) :
    shifted F χ C e hUV E u s =ᵐ[volume] fun X =>
      PauliMagneticOperator.quantum F χ hUV C e u s X -
        (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X := by
  have hs := Lp.coeFn_sub (PauliMagneticOperator.quantum F χ hUV C e u s)
    ((E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
  have hm := Lp.coeFn_smul (E : ℂ) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
  exact hs.trans (hm.mono fun X hX => congrArg
    (fun z : PhotonFock => PauliMagneticOperator.quantum F χ hUV C e u s X - z) hX)

def radiationCoefficient (hUV : CarlemanUV χ) (r₀ : ℝ) : ℝ :=
  2 * PauliCarlemanQuantum.radiationCoefficient (N := N) F χ e hUV r₀

def massCoefficient (hUV : CarlemanUV χ) (E σ : ℝ) : ℝ :=
  2 * PauliCarlemanQuantum.massCoefficient (N := N) F χ e hUV σ + 1040 * E ^ 2 * σ

theorem radiationCoefficient_nonneg (hUV : CarlemanUV χ) (r₀ : ℝ) :
    0 ≤ radiationCoefficient (N := N) F χ e hUV r₀ :=
  mul_nonneg (by norm_num) (PauliCarlemanQuantum.radiationCoefficient_nonneg F χ e hUV r₀)

theorem massCoefficient_nonneg (hUV : CarlemanUV χ) (E : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    0 ≤ massCoefficient (N := N) F χ e hUV E σ :=
  add_nonneg (mul_nonneg (by norm_num) (PauliCarlemanQuantum.massCoefficient_nonneg F χ e hUV hσ))
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hσ)

variable {O₀ : Configuration N} {ρ : ℝ} (a : PhysicalLocalExternalCoefficients.Data O₀ ρ)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))

/-- The shifted quantum term is an actual L2 source and satisfies the
uniform tau-decaying estimate needed in the full Pauli absorption. -/
theorem source_bound_of_estimate (hUV : CarlemanUV χ) (E : ℝ)
    {O : Configuration N} {family : BufferedFamily O} {R r₀ τ α σ C₂ C₂e : ℝ}
    {hR : 0 < R} (hτ : 0 < τ) (hα : 0 < α) (hRr : R ≤ r₀) (hrone : r₀ < 1)
    (hσ : 0 ≤ σ)
    (hratio : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      r ^ (4 : ℝ) / CarlemanWeights.beta α (-Real.log r) ≤ σ)
    (u : PauliReference.Ref N)
    (hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s))
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (he : PauliCarlemanFinite.Estimate F χ C e a spectral family R hR τ α C₂ C₂e u hu f)
    (hsupp : ∀ s, AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R) :
    IntegrableOn (fun X => ∑ s, sourceEnergy O τ α (shifted F χ C e hUV E u s) X)
        (Metric.ball O R) ∧
      (∫ X in Metric.ball O R, ∑ s, sourceEnergy O τ α (shifted F χ C e hUV E u s) X) ≤
        (radiationCoefficient (N := N) F χ e hUV r₀ * τ ^ (-1 : ℝ) +
          massCoefficient (N := N) F χ e hUV E σ * τ ^ (-3 : ℝ)) *
            ∑ s, ∫ X in Metric.ball O R, sourceEnergy O τ α (f s) X := by
  have hq := PauliCarlemanQuantum.source_bound_of_estimate F χ C e a spectral hUV
    hτ hα hRr hrone hσ hratio u hu f he hsupp
  have hm := PauliCarlemanQuantum.mass_source_bound_of_estimate F χ C e a spectral
    hτ hα hRr hrone hσ hratio u hu f he hsupp
  have hw := PhysicalSourceAbsorption.centeredSourceWeight_measurable O τ α
  have hmeas : AEStronglyMeasurable
      (fun X => ∑ s, sourceEnergy O τ α (shifted F χ C e hUV E u s) X)
      (volume.restrict (Metric.ball O R)) :=
    (Finset.univ.aestronglyMeasurable_fun_sum fun s _ => hw.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable (shifted F χ C e hUV E u s)).norm.pow 2)).restrict
  have hb := finite_shift_bound (volume.restrict (Metric.ball O R)) (centeredSourceWeight O τ α)
    (fun s X => PauliMagneticOperator.quantum F χ hUV C e u s X)
    (fun s X => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
    (fun s X => shifted F χ C e hUV E u s X) E
    (ae_of_all _ (PhysicalSourceAbsorption.centeredSourceWeight_nonneg O τ α))
    (fun s => ae_restrict_of_ae (shifted_ae F χ C e hUV E u s))
    hmeas hq.1 hm.1
  exact ⟨hb.1, hb.2.trans (shift_arithmetic hq.2 hm.2)⟩

end PfHk.PauliCarlemanQuantumShift

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
