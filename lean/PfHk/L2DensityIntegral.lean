import PfHk.L2QuadraticForms

/-! Combination of the actual L2 quadratic densities into one integrable
scalar density. -/

noncomputable section
namespace PfHk.L2QuadraticForms

open MeasureTheory
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

theorem real_smul_normed_ae {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (u : Lp E 2 μ) {f : X → E}
    (hu : u =ᵐ[μ] f) : c • u =ᵐ[μ] fun x => c • f x := by
  filter_upwards [Lp.coeFn_smul c u, hu] with x hx hy
  rw [hx, Pi.smul_apply, hy]

theorem complex_smul_normed_ae {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (u : Lp E 2 μ) {f : X → E}
    (hu : u =ᵐ[μ] f) : c • u =ᵐ[μ] fun x => c • f x := by
  filter_upwards [Lp.coeFn_smul c u, hu] with x hx hy
  rw [hx, Pi.smul_apply, hy]

variable {X H J : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype J]

theorem real_smul_ae (c : ℝ) (u : Lp H 2 μ) {f : X → H}
    (hu : u =ᵐ[μ] f) : c • u =ᵐ[μ] fun x => c • f x := by
  filter_upwards [Lp.coeFn_smul c u, hu] with x hx hy
  rw [hx, Pi.smul_apply, hy]

theorem combined_density_eq_integral (A B C : ℝ) (u v : Lp H 2 μ) (p : J → Lp H 2 μ)
    (f g : X → H) (h : X → J → H) (R : X → ℝ)
    (hu : u =ᵐ[μ] f) (hv : v =ᵐ[μ] g) (hp : ∀ j, p j =ᵐ[μ] fun x => h x j)
    (hR : Integrable R μ) :
    A*‖u‖^2 + B*(‖v‖^2 + ∑ j, ‖p j‖^2) + C*(∫ x, R x ∂μ) =
      ∫ x, A*‖f x‖^2 + B*(‖g x‖^2 + ∑ j, ‖h x j‖^2) + C*R x ∂μ := by
  have hu' : ‖u‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
    simpa only [one_mul] using scaled_norm_eq_integral 1 u hu
  have hv' : ‖v‖^2 = ∫ x, ‖g x‖^2 ∂μ := by
    simpa only [one_mul] using scaled_norm_eq_integral 1 v hv
  have hp' := sum_norm_eq_integral p hp
  have hf := norm_integrable u hu
  have hg := norm_integrable v hv
  have hh := sum_norm_integrable p hp
  have hmid : Integrable (fun x => ‖g x‖^2 + ∑ j, ‖h x j‖^2) μ := hg.add hh
  have hmidB : Integrable (fun x => B*(‖g x‖^2 + ∑ j, ‖h x j‖^2)) μ := hmid.const_mul B
  have hmassA : Integrable (fun x => A*‖f x‖^2) μ := hf.const_mul A
  have hleft : Integrable (fun x => A*‖f x‖^2 + B*(‖g x‖^2 + ∑ j, ‖h x j‖^2)) μ :=
    hmassA.add hmidB
  rw [integral_add hleft (hR.const_mul C),
    integral_add hmassA hmidB,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_add hg hh,
    hu', hv', hp']

end PfHk.L2QuadraticForms
