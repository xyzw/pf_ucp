import PfHk.WeightedNorm
import PfHk.CarlemanAlgebra

/-! Absorption for finite systems with coupled perturbations. Smallness
is required only for the sum of component source energies, so this result
does not assume that the Pauli spin components decouple. -/

noncomputable section
namespace PfHk.PauliCarlemanAbsorption

open MeasureTheory

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

variable {S X H : Type*} [Fintype S] [MeasurableSpace X] [NormedAddCommGroup H]
  {μ : Measure X}

def source (w : X → ℝ) (f : S → X → H) : ℝ :=
  ∑ s, ∫ x, w x * ‖f s x‖ ^ 2 ∂μ

theorem source_nonneg {w : X → ℝ} (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (f : S → X → H) : 0 ≤ source (μ := μ) w f :=
  Finset.sum_nonneg fun _s _ => integral_nonneg_of_ae (hw.mono fun _ hx =>
    mul_nonneg hx (sq_nonneg _))

theorem source_triangle {w : X → ℝ} {free full error : S → X → H}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hf : ∀ s, Integrable (fun x => w x * ‖free s x‖ ^ 2) μ)
    (hp : ∀ s, Integrable (fun x => w x * ‖full s x‖ ^ 2) μ)
    (he : ∀ s, Integrable (fun x => w x * ‖error s x‖ ^ 2) μ)
    (hop : ∀ s, free s =ᵐ[μ] fun x => full s x - error s x) :
    source (μ := μ) w free ≤
      2 * source (μ := μ) w full + 2 * source (μ := μ) w error := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
    (WeightedNorm.sub_integrable_bound hw (hf s).aestronglyMeasurable (hp s) (he s) (hop s)).2
  simpa only [source, Finset.sum_add_distrib,
    Finset.mul_sum] using h

theorem absorb {w : X → ℝ} {free full error : S → X → H}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hf : ∀ s, Integrable (fun x => w x * ‖free s x‖ ^ 2) μ)
    (hp : ∀ s, Integrable (fun x => w x * ‖full s x‖ ^ 2) μ)
    (he : ∀ s, Integrable (fun x => w x * ‖error s x‖ ^ 2) μ)
    (hop : ∀ s, free s =ᵐ[μ] fun x => full s x - error s x)
    (hsmall : source (μ := μ) w error ≤ source (μ := μ) w free / 4) :
    source (μ := μ) w free ≤ 4 * source (μ := μ) w full :=
  CarlemanAlgebra.perturbation_absorption (source_triangle hw hf hp he hop) hsmall

end PfHk.PauliCarlemanAbsorption
