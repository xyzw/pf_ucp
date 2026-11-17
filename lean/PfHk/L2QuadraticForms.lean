import GptLean.PhotonKernelLocalization

/-! Finite quadratic forms in L2 and their representative integrals. -/

noncomputable section
namespace PfHk.L2QuadraticForms

open MeasureTheory
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {X H ι : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype ι]

theorem smul_ae [NormedSpace ℂ H] (c : ℂ) (u : Lp H 2 μ) {f : X → H}
    (hu : u =ᵐ[μ] f) : c • u =ᵐ[μ] fun x => c • f x := by
  filter_upwards [Lp.coeFn_smul c u, hu] with x hx hy
  rw [hx, Pi.smul_apply, hy]

theorem add_smul_ae [NormedSpace ℂ H] (c : ℂ) (u v : Lp H 2 μ) {f : X → H}
    (hv : v =ᵐ[μ] f) : u + c • v =ᵐ[μ] fun x => u x + c • f x := by
  filter_upwards [Lp.coeFn_add u (c • v), smul_ae c v hv] with x hx hy
  rw [hx, Pi.add_apply, hy]

theorem norm_integrable (u : Lp H 2 μ) {f : X → H} (hu : u =ᵐ[μ] f) :
    Integrable (fun x => ‖f x‖ ^ 2) μ :=
  ((Lp.memLp u).norm.integrable_sq).congr (hu.mono fun _ h => congrArg (fun v => ‖v‖ ^ 2) h)

theorem inner_integrable (u v : Lp H 2 μ) {f g : X → H}
    (hu : u =ᵐ[μ] f) (hv : v =ᵐ[μ] g) :
    Integrable (fun x => 2 * inner ℝ (f x) (g x)) μ := by
  apply ((L2.integrable_inner (𝕜 := ℝ) u v).const_mul (2 : ℝ)).congr
  filter_upwards [hu, hv] with x hx hy
  rw [hx, hy]

theorem scaled_norm_eq_integral (c : ℝ) (u : Lp H 2 μ) {f : X → H}
    (hu : u =ᵐ[μ] f) : c * ‖u‖ ^ 2 = ∫ x, c * ‖f x‖ ^ 2 ∂μ := by
  rw [GptLean.PhotonKernelLocalization.l2_norm_sq_eq_integral, ← integral_const_mul]
  exact integral_congr_ae (hu.mono fun _ h => congrArg (fun v => c * ‖v‖ ^ 2) h)

theorem scaled_inner_eq_integral (c : ℝ) (u v : Lp H 2 μ) {f g : X → H}
    (hu : u =ᵐ[μ] f) (hv : v =ᵐ[μ] g) :
    c * inner ℝ u v = ∫ x, c * inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  rw [hx, hy]

theorem sum_norm_integrable (u : ι → Lp H 2 μ) {f : X → ι → H}
    (hu : ∀ j, u j =ᵐ[μ] fun x => f x j) :
    Integrable (fun x => ∑ j, ‖f x j‖ ^ 2) μ :=
  integrable_finsetSum _ fun j _ => norm_integrable (u j) (hu j)

theorem sum_inner_integrable (u v : ι → Lp H 2 μ) {f g : X → ι → H}
    (hu : ∀ j, u j =ᵐ[μ] fun x => f x j) (hv : ∀ j, v j =ᵐ[μ] fun x => g x j) :
    Integrable (fun x => ∑ j, 2 * inner ℝ (f x j) (g x j)) μ :=
  integrable_finsetSum _ fun j _ => inner_integrable (u j) (v j) (hu j) (hv j)

theorem sum_norm_eq_integral (u : ι → Lp H 2 μ) {f : X → ι → H}
    (hu : ∀ j, u j =ᵐ[μ] fun x => f x j) :
    (∑ j, ‖u j‖ ^ 2) = ∫ x, ∑ j, ‖f x j‖ ^ 2 ∂μ := by
  rw [integral_finsetSum _ fun j _ => norm_integrable (u j) (hu j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [GptLean.PhotonKernelLocalization.l2_norm_sq_eq_integral]
  exact integral_congr_ae ((hu j).mono fun _ h => congrArg (fun v => ‖v‖ ^ 2) h)

theorem sum_inner_eq_integral (u v : ι → Lp H 2 μ) {f g : X → ι → H}
    (hu : ∀ j, u j =ᵐ[μ] fun x => f x j) (hv : ∀ j, v j =ᵐ[μ] fun x => g x j) :
    (∑ j, 2 * inner ℝ (u j) (v j)) = ∫ x, ∑ j, 2 * inner ℝ (f x j) (g x j) ∂μ := by
  rw [integral_finsetSum _ fun j _ => inner_integrable (u j) (v j) (hu j) (hv j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hu j, hv j] with x hx hy
  rw [hx, hy]

end PfHk.L2QuadraticForms
