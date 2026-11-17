import PfHk.PauliMagneticOperator
import PfHk.PhysicalShiftedFormEnergyLp
import PfHk.PauliCurrent

/-! Integration of the actual Pauli contraction and current. -/

noncomputable section
namespace PfHk.PauliExternalEnergyLp

open MeasureTheory GptLean PfHk.PauliSpin PfHk.PauliCurrentAlgebra
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

variable {N : ℕ} {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}

theorem contraction_ae (n : Fin N) (d : Fin 3 → SpinIndex N → Lp H 2 μ)
    (s : SpinIndex N) :
    (fun x => contraction n d s x) =ᵐ[μ]
      fun x => contraction n (fun a t => d a t x) s := by
  simpa only [contraction, Finset.sum_apply] using
    PauliMagneticOperator.sum_sigma_ae μ n d (fun a t x => d a t x)
      (fun _ _ => Filter.EventuallyEq.rfl) s

theorem velocity_ae (n : Fin N) (d : Fin 3 → SpinIndex N → Lp H 2 μ)
    (a : Fin 3) (s : SpinIndex N) :
    (fun x => velocity n a d s x) =ᵐ[μ]
      fun x => velocity n a (fun b t => d b t x) s := by
  filter_upwards [PauliMagneticOperator.sigma_ae μ n a (contraction n d) s,
    ae_all_iff.mpr (contraction_ae n d)] with x hσ hd
  exact hσ.trans (congrArg (fun w => sigmaFamily n a w s) (funext hd))

theorem bundle_current_ae (n : Fin N) (u : SpinIndex N → Lp H 2 μ)
    (d : Fin 3 → SpinIndex N → Lp H 2 μ) (a : Fin 3) :
    (fun x => (inner ℂ (FiniteFiberL2.bundle u x)
      (FiniteFiberL2.bundle (velocity n a d) x)).re) =ᵐ[μ]
      fun x => current n (fun s => u s x) (fun b s => d b s x) a := by
  filter_upwards [FiniteFiberL2.bundle_ae u,
    FiniteFiberL2.bundle_ae (velocity n a d), ae_all_iff.mpr (velocity_ae n d a)]
      with x hu hd hv
  rw [hu, hd, PiLp.inner_apply, Complex.re_sum]
  exact Finset.sum_congr rfl fun s _ => congrArg (fun z : H => (inner ℂ (u s x) z).re) (hv s)

theorem kinetic_integrable (n : Fin N) (d : Fin 3 → SpinIndex N → Lp H 2 μ) :
    Integrable (fun x => kinetic n (fun a s => d a s x)) μ := by
  have h := (integrable_finsetSum Finset.univ (fun s _ =>
    (Lp.memLp (contraction n d s)).norm.integrable_sq)).const_mul (1 / 2 : ℝ)
  apply h.congr
  filter_upwards [ae_all_iff.mpr (contraction_ae n d)] with x hx
  exact congrArg (fun r : ℝ => (1 / 2 : ℝ) * r)
    (Finset.sum_congr rfl fun s _ => congrArg (fun z : H => ‖z‖ ^ 2) (hx s))

theorem kinetic_eq_integral (n : Fin N) (d : Fin 3 → SpinIndex N → Lp H 2 μ) :
    kinetic n d = ∫ x, kinetic n (fun a s => d a s x) ∂μ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  unfold kinetic
  rw [integral_const_mul]
  congr 1
  calc
    (∑ s, ‖contraction n d s‖ ^ 2) = ∑ s, ∫ x, ‖contraction n d s x‖ ^ 2 ∂μ :=
      Finset.sum_congr rfl fun s _ => PhotonKernelLocalization.l2_norm_sq_eq_integral _
    _ = ∫ x, ∑ s, ‖contraction n d s x‖ ^ 2 ∂μ :=
      (integral_finsetSum _ (fun s _ => (Lp.memLp (contraction n d s)).norm.integrable_sq)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr (contraction_ae n d)] with x hx
      exact Finset.sum_congr rfl fun s _ => congrArg (fun z : H => ‖z‖ ^ 2) (hx s)

theorem current_integrable (n : Fin N) (u : SpinIndex N → Lp H 2 μ)
    (d : Fin 3 → SpinIndex N → Lp H 2 μ) (a : Fin 3) (b : X → ℝ)
    (hb : ∀ s, MemLp (fun x => b x • u s x) 2 μ) :
    Integrable (fun x => b x * current n (fun s => u s x) (fun a s => d a s x) a) μ := by
  have h := integrable_finsetSum Finset.univ (fun s _ =>
    PhysicalShiftedFormEnergyLp.multiplier_cross_integrable (u s) (velocity n a d s) b (hb s))
  apply h.congr
  filter_upwards [ae_all_iff.mpr (velocity_ae n d a)] with x hx
  simp only [current, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => congrArg (fun z : H => b x * (inner ℂ (u s x) z).re) (hx s)

theorem square_integrable (u : SpinIndex N → Lp H 2 μ) (b : X → ℝ)
    (hb : ∀ s, MemLp (fun x => b x • u s x) 2 μ) :
    Integrable (fun x => b x ^ 2 * density (fun s => u s x)) μ := by
  simpa only [density, Finset.mul_sum] using
    integrable_finsetSum Finset.univ (fun s _ =>
      PhysicalShiftedFormEnergyLp.multiplier_square_integrable (u s) b (hb s))

theorem integrated_kinetic_shift (n : Fin N) (u : SpinIndex N → Lp H 2 μ)
    (d d' : Fin 3 → SpinIndex N → Lp H 2 μ) (b : Fin 3 → X → ℝ)
    (hb : ∀ a s, MemLp (fun x => b a x • u s x) 2 μ)
    (hd : ∀ a s, (fun x => d' a s x) =ᵐ[μ]
      fun x => d a s x + (b a x : ℂ) • u s x) :
    kinetic n d' = kinetic n d +
      (∑ a, ∫ x, b a x * current n (fun s => u s x) (fun a s => d a s x) a ∂μ) +
      (1 / 2 : ℝ) * ∑ a, ∫ x, b a x ^ 2 * density (fun s => u s x) ∂μ := by
  have he : (fun x => kinetic n (fun a s => d' a s x)) =ᵐ[μ]
      fun x => kinetic n (fun a s => d a s x) +
        (∑ a, b a x * current n (fun s => u s x) (fun a s => d a s x) a) +
        (1 / 2 : ℝ) * ∑ a, b a x ^ 2 * density (fun s => u s x) := by
    filter_upwards [ae_all_iff.mpr (fun a => ae_all_iff.mpr (hd a))] with x hx
    have hs := kinetic_shift n (fun s => u s x) (fun a s => d a s x) (fun a => b a x)
    simpa only [← Finset.sum_mul, mul_assoc] using
      (congrArg (kinetic n) (funext fun a => funext (hx a))).trans hs
  have hj := integrable_finsetSum Finset.univ (fun a _ => current_integrable n u d a (b a) (hb a))
  have hs := integrable_finsetSum Finset.univ (fun a _ => square_integrable u (b a) (hb a))
  have hadd := integral_add ((kinetic_integrable n d).add hj) (hs.const_mul (1 / 2 : ℝ))
  have hadd' := integral_add (kinetic_integrable n d) hj
  simp only [Pi.add_apply] at hadd hadd'
  rw [kinetic_eq_integral n d', integral_congr_ae he, hadd, hadd', integral_const_mul,
    integral_finsetSum _ (fun a _ => current_integrable n u d a (b a) (hb a)),
    integral_finsetSum _ (fun a _ => square_integrable u (b a) (hb a)),
    ← kinetic_eq_integral n d]

end PfHk.PauliExternalEnergyLp
