import PfHk.PauliSpin

/-! Linear-map compatibility and bounded operators for the concrete Pauli
spin action. These statements apply to electronic cutoffs, derivatives,
and photon operators on their common linear domains. -/

noncomputable section
namespace PfHk.PauliSpin

open scoped BigOperators
variable {N : ℕ}

/-- A Cartesian unit vector, used to recover one Pauli matrix. -/
def unit (μ : Fin 3) : Fin 3 → ℝ := fun ν => if ν = μ then 1 else 0

section Algebra
variable {H K : Type*} [AddCommGroup H] [Module ℂ H]
  [AddCommGroup K] [Module ℂ K]

theorem fieldFamily_unit (n : Fin N) (μ : Fin 3) (u : SpinIndex N → H) :
    fieldFamily n (unit μ) u = sigmaFamily n μ u := by
  funext s
  rw [fieldFamily_eq_sum]
  simp [unit, apply_ite]

/-- The spin matrices commute with every linear map on the non-spin fiber. -/
theorem sigmaFamily_map (n : Fin N) (μ : Fin 3) (L : H →ₗ[ℂ] K)
    (u : SpinIndex N → H) :
    sigmaFamily n μ (fun s => L (u s)) = fun s => L (sigmaFamily n μ u s) := by
  funext s
  simp only [sigmaFamily]
  split_ifs <;> simp

theorem fieldFamily_map (n : Fin N) (b : Fin 3 → ℝ) (L : H →ₗ[ℂ] K)
    (u : SpinIndex N → H) :
    fieldFamily n b (fun s => L (u s)) = fun s => L (fieldFamily n b u s) := by
  funext s
  simp [fieldFamily]

theorem sigmaFamily_square (n : Fin N) (μ : Fin 3) (u : SpinIndex N → H) :
    sigmaFamily n μ (sigmaFamily n μ u) = u := by
  have h := fieldFamily_square n (unit μ) u
  simpa [fieldFamily_unit, unit, apply_ite] using h

end Algebra

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sigmaFamily_sum_norm_sq (n : Fin N) (μ : Fin 3) (u : SpinIndex N → H) :
    (∑ s, ‖sigmaFamily n μ u s‖^2) = ∑ s, ‖u s‖^2 := by
  have h := fieldFamily_sum_norm_sq n (unit μ) u
  simpa [fieldFamily_unit, unit, apply_ite] using h

theorem field_unit (n : Fin N) (μ : Fin 3) (u : Fiber N H) :
    field n (unit μ) u = sigma n μ u := by
  apply PiLp.ext
  intro s
  exact congrFun (fieldFamily_unit n μ (fun s => u s)) s

theorem sigma_norm_sq (n : Fin N) (μ : Fin 3) (u : Fiber N H) :
    ‖sigma n μ u‖^2 = ‖u‖^2 := by
  have h := field_norm_sq n (unit μ) u
  simpa [field_unit, unit, apply_ite] using h

@[simp] theorem sigma_norm (n : Fin N) (μ : Fin 3) (u : Fiber N H) :
    ‖sigma n μ u‖ = ‖u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (sigma_norm_sq n μ u)

def fieldLinear (n : Fin N) (b : Fin 3 → ℝ) : Fiber N H →ₗ[ℂ] Fiber N H where
  toFun := field n b
  map_add' u v := by
    apply PiLp.ext
    intro s
    exact congrFun (fieldFamily_add n b (fun s => u s) (fun s => v s)) s
  map_smul' c u := by
    apply PiLp.ext
    intro s
    exact congrFun (fieldFamily_smul n b c (fun s => u s)) s

theorem field_norm_le (n : Fin N) (b : Fin 3 → ℝ) (u : Fiber N H) :
    ‖field n b u‖ ≤ Real.sqrt (∑ μ : Fin 3, (b μ)^2) * ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [field_norm_sq, mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]

/-- Bounded Pauli multiplication on the genuine finite Hilbert amplification. -/
def fieldCLM (n : Fin N) (b : Fin 3 → ℝ) : Fiber N H →L[ℂ] Fiber N H :=
  (fieldLinear n b).mkContinuous (Real.sqrt (∑ μ : Fin 3, (b μ)^2)) (field_norm_le n b)

@[simp] theorem fieldCLM_apply (n : Fin N) (b : Fin 3 → ℝ) (u : Fiber N H) :
    fieldCLM n b u = field n b u := rfl

def sigmaCLM (n : Fin N) (μ : Fin 3) : Fiber N H →L[ℂ] Fiber N H :=
  fieldCLM n (unit μ)

@[simp] theorem sigmaCLM_apply (n : Fin N) (μ : Fin 3) (u : Fiber N H) :
    sigmaCLM n μ u = sigma n μ u := field_unit n μ u

end Hilbert
end PfHk.PauliSpin
