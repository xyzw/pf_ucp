import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
The Fubini step in the proof of `thm-hk-nonvanishing` in `pf_ucp.tex`.
No regularity of the one-body multiplier is needed. An almost-everywhere
constant sum on a finite configuration space forces each summand to be
constant almost everywhere, with the exact constant given by particle number.
The physical passage from weak equations to scalar uniqueness is proved in
`PhysicalScalarWeakUniqueness` using these Fubini lemmas.
-/

namespace PfHk.ScalarUniqueness

open MeasureTheory Filter
open scoped ContDiff

variable {X : Type*} [MeasurableSpace X]

/-- A finite product of a nonzero sigma-finite measure is nonzero,
including the empty product. -/
theorem pi_measure_ne_zero (μ : Measure X) [SigmaFinite μ]
    (hμ : μ ≠ 0) (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ) ≠ 0 := by
  intro h
  have hzero : (Measure.pi (fun _ : Fin n => μ)) Set.univ = 0 := by rw [h]; simp
  rw [Measure.pi_univ] at hzero
  have hnonzero : (∏ _ : Fin n, μ Set.univ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun _ _ => Measure.measure_univ_eq_zero.not.mpr hμ
  exact hnonzero hzero

/-- Fixing all but the first coordinate by Fubini makes a one-body
multiplier constant. The measure need not be finite. -/
theorem ae_constant_of_sum_eq_succ (μ : Measure X) [SigmaFinite μ]
    (hμ : μ ≠ 0) (n : ℕ) (w : X → ℝ) (c : ℝ)
    (hsum : ∀ᵐ x ∂Measure.pi (fun _ : Fin (n + 1) => μ),
      ∑ i, w (x i) = c) :
    ∃ d : ℝ, (∀ᵐ x ∂μ, w x = d) ∧ (n + 1 : ℝ) * d = c := by
  let ν : Measure (Fin n → X) := Measure.pi (fun _ => μ)
  have : (ae ν).NeBot := ae_neBot.mpr (pi_measure_ne_zero μ hμ n)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
  have he : MeasurePreserving e.symm (μ.prod ν)
      (Measure.pi (fun _ : Fin (n + 1) => μ)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm e
  have hp : ∀ᵐ p ∂μ.prod ν, ∑ i, w (e.symm p i) = c :=
    he.quasiMeasurePreserving.ae hsum
  have hswap : ∀ᵐ p ∂ν.prod μ, ∑ i, w (e.symm (p.2, p.1) i) = c :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hp
  obtain ⟨tail, htail⟩ := (Measure.ae_ae_of_ae_prod hswap).exists
  let d := c - ∑ i, w (tail i)
  have hd : ∀ᵐ x ∂μ, w x = d := by
    filter_upwards [htail] with x hx
    have hs : w x + ∑ i, w (tail i) = c := by
      simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.sum_univ_succAbove _ 0] using hx
    dsimp [d]
    linarith
  have hcoords : ∀ᵐ x ∂Measure.pi (fun _ : Fin (n + 1) => μ),
      ∀ i, w (x i) = d :=
    ae_all_iff.mpr fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (n + 1) => μ) (i := i)).eventually hd
  have : (ae (Measure.pi (fun _ : Fin (n + 1) => μ))).NeBot :=
    ae_neBot.mpr (pi_measure_ne_zero μ hμ (n + 1))
  obtain ⟨x, hx, hxd⟩ := (hsum.and hcoords).exists
  refine ⟨d, hd, ?_⟩
  simpa [hxd, nsmul_eq_mul] using hx

/-- The exact scalar-potential constant in the Hohenberg--Kohn proof.
This is valid for any nonzero sigma-finite one-particle measure. -/
theorem ae_eq_div_of_sum_eq (μ : Measure X) [SigmaFinite μ]
    (hμ : μ ≠ 0) {N : ℕ} (hN : 0 < N) (w : X → ℝ) (c : ℝ)
    (hsum : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ), ∑ i, w (x i) = c) :
    ∀ᵐ x ∂μ, w x = c / N := by
  cases N with
  | zero => simp at hN
  | succ n =>
    obtain ⟨d, hd, hdc⟩ := ae_constant_of_sum_eq_succ μ hμ n w c hsum
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    have heq : d = c / (n + 1 : ℝ) := (eq_div_iff hn).mpr (by linarith)
    simpa only [heq, Nat.cast_add, Nat.cast_one] using hd

/-- The nonvanishing fiber cancels from the scalar multiplier equation. -/
theorem ae_sum_eq_of_multiplier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure X) {N : ℕ} (w : X → ℝ)
    (c : ℝ) (ψ : (Fin N → X) → E)
    (hψ : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ), ψ x ≠ 0)
    (hmul : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      ((∑ i, w (x i)) - c) • ψ x = 0) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ), ∑ i, w (x i) = c := by
  filter_upwards [hψ, hmul] with x hx hm
  exact sub_eq_zero.mp ((smul_eq_zero.mp hm).resolve_right hx)

/-- Scalar uniqueness after the weak multiplier equation has been
identified almost everywhere and the wavefunction is nonvanishing. -/
theorem potential_difference_constant {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure X) [SigmaFinite μ]
    (hμ : μ ≠ 0) {N : ℕ} (hN : 0 < N)
    (v₁ v₂ : X → ℝ) (E₁ E₂ : ℝ) (ψ : (Fin N → X) → E)
    (hψ : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ), ψ x ≠ 0)
    (hmul : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      ((∑ i, (v₁ (x i) - v₂ (x i))) - (E₁ - E₂)) • ψ x = 0) :
    ∀ᵐ x ∂μ, v₁ x = v₂ x + (E₁ - E₂) / N := by
  have hs := ae_sum_eq_of_multiplier μ (fun x => v₁ x - v₂ x) (E₁ - E₂) ψ hψ hmul
  have hd := ae_eq_div_of_sum_eq μ hμ hN (fun x => v₁ x - v₂ x) (E₁ - E₂) hs
  filter_upwards [hd] with x hx
  linarith

/-- Scalar form integrability and local integrability of a potential
control the corresponding vector-valued product. Apply this lemma to
restrictions of volume to bounded configuration sets. -/
theorem integrable_multiplier_of_form_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (w : X → ℝ) (ψ : X → E)
    (hw : Integrable w μ)
    (hform : Integrable (fun x => |w x| * ‖ψ x‖ ^ 2) μ)
    (hψ : AEStronglyMeasurable ψ μ) :
    Integrable (fun x => w x • ψ x) μ := by
  have hmajor : Integrable (fun x => (|w x| + |w x| * ‖ψ x‖ ^ 2) / 2) μ := by
    simpa only [Real.norm_eq_abs, Pi.add_apply] using (hw.norm.add hform).div_const 2
  refine hmajor.mono' (hw.aestronglyMeasurable.smul hψ) (ae_of_all μ fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  have ha := abs_nonneg (w x)
  have hs := sq_nonneg (‖ψ x‖ - 1)
  nlinarith [mul_nonneg ha hs]

/-- The standard fundamental lemma for distributions supplies the
almost-everywhere multiplier equation, after subtraction of the weak
Hamiltonian equations has supplied the displayed test identity. -/
theorem potential_difference_constant_of_weak_equation
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [SigmaFinite μ] (hμ : μ ≠ 0) {N : ℕ} (hN : 0 < N)
    (v₁ v₂ : X → ℝ) (E₁ E₂ : ℝ) (ψ : (Fin N → X) → E)
    (hψ : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ), ψ x ≠ 0)
    (hlocal : LocallyIntegrable
      (fun x : Fin N → X => ((∑ i, (v₁ (x i) - v₂ (x i))) - (E₁ - E₂)) • ψ x)
      (Measure.pi (fun _ => μ)))
    (hweak : ∀ (g : (Fin N → X) → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (((∑ i, (v₁ (x i) - v₂ (x i))) - (E₁ - E₂)) • ψ x)
        ∂Measure.pi (fun _ => μ) = 0) :
    ∀ᵐ x ∂μ, v₁ x = v₂ x + (E₁ - E₂) / N := by
  exact potential_difference_constant μ hμ hN v₁ v₂ E₁ E₂ ψ hψ
    (ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal hweak)

end PfHk.ScalarUniqueness
