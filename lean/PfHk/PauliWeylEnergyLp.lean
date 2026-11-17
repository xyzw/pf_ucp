import PfHk.PauliExternalEnergyLp
import PfHk.PauliCurrentCovariance

/-! Integration of a Pauli kinetic shift through a photon isometry. -/

noncomputable section
namespace PfHk.PauliWeylEnergyLp

open MeasureTheory GptLean PfHk.PauliSpin PfHk.PauliCurrentAlgebra
  PfHk.PauliExternalEnergyLp

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

variable {N : ℕ} {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}

theorem bounded_multiplier (u : Lp H 2 μ) (b : X → ℝ)
    (hb : AEStronglyMeasurable b μ) {B : ℝ} (hB : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) :
    MemLp (fun x => b x • u x) 2 μ := by
  apply (Lp.memLp u).of_le_mul (c := B) (hb.smul (Lp.aestronglyMeasurable u))
  filter_upwards [hB] with x hx
  change ‖b x • u x‖ ≤ B * ‖u x‖
  simpa only [norm_smul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (u x))

theorem integrated_kinetic_isometry_shift (n : Fin N) (L : H →ₗᵢ[ℂ] H)
    (u : SpinIndex N → Lp H 2 μ) (d d' : Fin 3 → SpinIndex N → Lp H 2 μ)
    (b : Fin 3 → X → ℝ) (hb : ∀ a s, MemLp (fun x => b a x • u s x) 2 μ)
    (hd : ∀ a s, (fun x => d' a s x) =ᵐ[μ]
      fun x => L (d a s x + (b a x : ℂ) • u s x)) :
    kinetic n d' = kinetic n d +
      (∑ a, ∫ x, b a x * current n (fun s => u s x) (fun a s => d a s x) a ∂μ) +
      (1 / 2 : ℝ) * ∑ a, ∫ x, b a x ^ 2 * density (fun s => u s x) ∂μ := by
  have he : (fun x => kinetic n (fun a s => d' a s x)) =ᵐ[μ]
      fun x => kinetic n (fun a s => d a s x) +
        (∑ a, b a x * current n (fun s => u s x) (fun a s => d a s x) a) +
        (1 / 2 : ℝ) * ∑ a, b a x ^ 2 * density (fun s => u s x) := by
    filter_upwards [ae_all_iff.mpr (fun a => ae_all_iff.mpr (hd a))] with x hx
    have hs := kinetic_isometry_shift n L (fun s => u s x)
      (fun a s => d a s x) (fun a => b a x)
    simpa only [← Finset.sum_mul, mul_assoc] using
      (congrArg (kinetic n) (funext fun a => funext (hx a))).trans hs
  have hj := integrable_finsetSum Finset.univ
    (fun a _ => current_integrable n u d a (b a) (hb a))
  have hs := integrable_finsetSum Finset.univ (fun a _ => square_integrable u (b a) (hb a))
  have hadd := integral_add ((kinetic_integrable n d).add hj) (hs.const_mul (1 / 2 : ℝ))
  have hadd' := integral_add (kinetic_integrable n d) hj
  simp only [Pi.add_apply] at hadd hadd'
  rw [kinetic_eq_integral n d', integral_congr_ae he, hadd, hadd', integral_const_mul,
    integral_finsetSum _ (fun a _ => current_integrable n u d a (b a) (hb a)),
    integral_finsetSum _ (fun a _ => square_integrable u (b a) (hb a)),
    ← kinetic_eq_integral n d]

end PfHk.PauliWeylEnergyLp
