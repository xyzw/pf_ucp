import PfHk.PauliSpin
import PfHk.FiniteWeightedSource

/-! The actual classical Zeeman matrix multiplier and its finite-component
bound. The spin dimension does not enter the constant. -/

noncomputable section
namespace PfHk.PauliMagneticClassical

open MeasureTheory PfHk.PauliSpin

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def zeeman (B : Fin N → Fin 3 → ℝ) (u : SpinIndex N → H) (s : SpinIndex N) : H :=
  ((1 / 2 : ℝ) : ℂ) • ∑ n, fieldFamily n (B n) u s

theorem norm_sq_le (B : Fin N → Fin 3 → ℝ) (u : SpinIndex N → H) :
    (∑ s, ‖zeeman B u s‖ ^ 2) ≤
      ((N : ℝ) / 4) * ∑ n, ∑ μ : Fin 3, ∑ s, ‖(B n μ : ℂ) • u s‖ ^ 2 := by
  classical
  have hn (s : SpinIndex N) := FiniteWeightedSource.norm_sum_sq
    (Finset.univ : Finset (Fin N)) (fun n => fieldFamily n (B n) u s)
  have hsum : (∑ s, ‖∑ n, fieldFamily n (B n) u s‖ ^ 2) ≤
      (N : ℝ) * ∑ n, ∑ s, ‖fieldFamily n (B n) u s‖ ^ 2 := by
    rw [← Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_le_sum (fun s _ => by simpa using hn s)
  have heq (n : Fin N) : (∑ s, ‖fieldFamily n (B n) u s‖ ^ 2) =
      ∑ μ : Fin 3, ∑ s, ‖(B n μ : ℂ) • u s‖ ^ 2 := by
    rw [fieldFamily_sum_norm_sq]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [heq] at hsum
  have hscale := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 4)
  calc
    _ = (1 / 4 : ℝ) * ∑ s, ‖∑ n, fieldFamily n (B n) u s‖ ^ 2 := by
      simp only [zeeman, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
        Finset.mul_sum]
      norm_num
    _ ≤ _ := hscale.trans_eq (by ring)

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- The weighted matrix error is integrable whenever its scalar component
products are, and is bounded by those actual weighted scalar products. -/
theorem weighted_source_bound
    (B : Fin N → Fin 3 → X → ℝ) (u : X → SpinIndex N → H) (w : X → ℝ)
    (hw : ∀ᵐ x ∂ν, 0 ≤ w x)
    (hm : AEStronglyMeasurable
      (fun x => w x * ∑ s, ‖zeeman (fun n μ => B n μ x) (u x) s‖ ^ 2) ν)
    (hi : ∀ n μ s, Integrable (fun x => w x * ‖(B n μ x : ℂ) • u x s‖ ^ 2) ν) :
    Integrable (fun x => w x * ∑ s, ‖zeeman (fun n μ => B n μ x) (u x) s‖ ^ 2) ν ∧
      (∫ x, w x * ∑ s, ‖zeeman (fun n μ => B n μ x) (u x) s‖ ^ 2 ∂ν) ≤
        ((N : ℝ) / 4) * ∑ n, ∑ μ : Fin 3, ∑ s,
          ∫ x, w x * ‖(B n μ x : ℂ) • u x s‖ ^ 2 ∂ν := by
  classical
  let majorant := fun x => ((N : ℝ) / 4) * ∑ n, ∑ μ : Fin 3, ∑ s,
    w x * ‖(B n μ x : ℂ) • u x s‖ ^ 2
  have hmajor : Integrable majorant ν :=
    (integrable_finsetSum _ (fun n _ => integrable_finsetSum _ (fun μ _ =>
      integrable_finsetSum _ (fun s _ => hi n μ s)))).const_mul _
  have hb : ∀ᵐ x ∂ν,
      w x * ∑ s, ‖zeeman (fun n μ => B n μ x) (u x) s‖ ^ 2 ≤ majorant x := by
    filter_upwards [hw] with x hx
    apply (mul_le_mul_of_nonneg_left (norm_sq_le (fun n μ => B n μ x) (u x)) hx).trans_eq
    calc
      w x * ((N : ℝ) / 4 * ∑ n, ∑ μ : Fin 3, ∑ s,
          ‖(B n μ x : ℂ) • u x s‖ ^ 2) =
        ((N : ℝ) / 4) * (w x * ∑ n, ∑ μ : Fin 3, ∑ s,
          ‖(B n μ x : ℂ) • u x s‖ ^ 2) := by ring
      _ = majorant x := by simp only [majorant, Finset.mul_sum]
  have hnonneg : ∀ᵐ x ∂ν, 0 ≤ w x * ∑ s,
      ‖zeeman (fun n μ => B n μ x) (u x) s‖ ^ 2 :=
    hw.mono fun x hx => mul_nonneg hx (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hz : Integrable (fun x => w x * ∑ s,
      ‖zeeman (fun n μ => B n μ x) (u x) s‖ ^ 2) ν := hmajor.mono' hm (by
    filter_upwards [hb, hnonneg] with x hbx h0
    simpa only [Real.norm_of_nonneg h0] using hbx)
  refine ⟨hz, (integral_mono_ae hz hmajor hb).trans_eq ?_⟩
  dsimp [majorant]
  rw [integral_const_mul]
  congr 1
  calc
    _ = ∑ n, ∫ x, ∑ μ : Fin 3, ∑ s, w x * ‖(B n μ x : ℂ) • u x s‖ ^ 2 ∂ν :=
      integral_finsetSum Finset.univ (fun n _ =>
        integrable_finsetSum Finset.univ (fun μ _ =>
          integrable_finsetSum Finset.univ (fun s _ => hi n μ s)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      calc
        _ = ∑ μ : Fin 3, ∫ x, ∑ s, w x * ‖(B n μ x : ℂ) • u x s‖ ^ 2 ∂ν :=
          integral_finsetSum Finset.univ (fun μ _ =>
            integrable_finsetSum Finset.univ (fun s _ => hi n μ s))
        _ = _ := Finset.sum_congr rfl (fun μ _ =>
          integral_finsetSum Finset.univ (fun s _ => hi n μ s))

end PfHk.PauliMagneticClassical
