import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Concrete finite electron spin and the local Pauli action. The coefficient
space is the actual set of two-valued spin configurations. The photon fiber
may be any complex inner product space. -/

noncomputable section
namespace PfHk.PauliSpin

open scoped BigOperators ComplexConjugate

abbrev SpinIndex (N : ℕ) := Fin N → Fin 2

variable {N : ℕ}

/-- Reverse the spin of the specified electron. -/
def flip (n : Fin N) (s : SpinIndex N) : SpinIndex N :=
  Function.update s n (if s n = 0 then 1 else 0)

@[simp] theorem flip_apply_same (n : Fin N) (s : SpinIndex N) :
    flip n s n = if s n = 0 then 1 else 0 := by
  simp [flip]

@[simp] theorem flip_apply_ne (n m : Fin N) (s : SpinIndex N) (h : m ≠ n) :
    flip n s m = s m := by
  simp [flip, h]

@[simp] theorem flip_flip (n : Fin N) (s : SpinIndex N) : flip n (flip n s) = s := by
  funext m
  by_cases h : m = n
  · subst m
    generalize hs : s n = t
    fin_cases t <;> simp_all [flip]
  · simp [flip_apply_ne, h]

def flipEquiv (n : Fin N) : Equiv.Perm (SpinIndex N) where
  toFun := flip n
  invFun := flip n
  left_inv := flip_flip n
  right_inv := flip_flip n

/-- The eigenvalue of the third Pauli matrix at the selected spin. -/
def sign (n : Fin N) (s : SpinIndex N) : ℂ := if s n = 0 then 1 else -1

@[simp] theorem sign_flip (n : Fin N) (s : SpinIndex N) :
    sign n (flip n s) = - sign n s := by
  simp only [sign, flip_apply_same]
  split_ifs <;> norm_num at *

@[simp] theorem sign_sq (n : Fin N) (s : SpinIndex N) : sign n s ^ 2 = 1 := by
  simp only [sign]
  split_ifs <;> norm_num

@[simp] theorem conj_sign (n : Fin N) (s : SpinIndex N) : conj (sign n s) = sign n s := by
  simp only [sign]
  split_ifs <;> simp

section Algebra
variable {H : Type*} [AddCommGroup H] [Module ℂ H]

/-- The three Pauli matrices on coordinate families. -/
def sigmaFamily (n : Fin N) (μ : Fin 3) (u : SpinIndex N → H) : SpinIndex N → H :=
  if μ = 0 then fun s => u (flip n s)
  else if μ = 1 then fun s => (-Complex.I * sign n s) • u (flip n s)
  else fun s => sign n s • u s

/-- Contraction of the local Pauli matrices with a real three-vector. -/
def fieldFamily (n : Fin N) (b : Fin 3 → ℝ) (u : SpinIndex N → H) : SpinIndex N → H :=
  fun s => ((b 2 : ℂ) * sign n s) • u s +
    ((b 0 : ℂ) - Complex.I * (b 1 : ℂ) * sign n s) • u (flip n s)

@[simp] theorem sigmaFamily_zero (n : Fin N) (u : SpinIndex N → H) (s : SpinIndex N) :
    sigmaFamily n 0 u s = u (flip n s) := by simp [sigmaFamily]

@[simp] theorem sigmaFamily_one (n : Fin N) (u : SpinIndex N → H) (s : SpinIndex N) :
    sigmaFamily n 1 u s = (-Complex.I * sign n s) • u (flip n s) := by simp [sigmaFamily]

@[simp] theorem sigmaFamily_two (n : Fin N) (u : SpinIndex N → H) (s : SpinIndex N) :
    sigmaFamily n 2 u s = sign n s • u s := by simp [sigmaFamily]

theorem sigmaFamily_add (n : Fin N) (μ : Fin 3) (u v : SpinIndex N → H) :
    sigmaFamily n μ (u + v) = sigmaFamily n μ u + sigmaFamily n μ v := by
  funext s
  simp only [sigmaFamily]
  split_ifs <;> simp [smul_add]

theorem sigmaFamily_smul (n : Fin N) (μ : Fin 3) (c : ℂ) (u : SpinIndex N → H) :
    sigmaFamily n μ (c • u) = c • sigmaFamily n μ u := by
  funext s
  simp only [sigmaFamily]
  split_ifs <;> simp [smul_smul, mul_comm]

theorem fieldFamily_eq_sum (n : Fin N) (b : Fin 3 → ℝ) (u : SpinIndex N → H)
    (s : SpinIndex N) :
    fieldFamily n b u s = ∑ μ : Fin 3, (b μ : ℂ) • sigmaFamily n μ u s := by
  simp [Fin.sum_univ_succ, fieldFamily, sub_smul]
  module

theorem fieldFamily_add (n : Fin N) (b : Fin 3 → ℝ) (u v : SpinIndex N → H) :
    fieldFamily n b (u + v) = fieldFamily n b u + fieldFamily n b v := by
  funext s
  simp [fieldFamily, smul_add]
  abel

theorem fieldFamily_smul (n : Fin N) (b : Fin 3 → ℝ) (c : ℂ) (u : SpinIndex N → H) :
    fieldFamily n b (c • u) = c • fieldFamily n b u := by
  funext s
  simp [fieldFamily, smul_add, smul_smul, mul_comm]

/-- The square of the local Pauli contraction is the scalar squared length. -/
theorem fieldFamily_square (n : Fin N) (b : Fin 3 → ℝ) (u : SpinIndex N → H) :
    fieldFamily n b (fieldFamily n b u) =
      ((∑ μ : Fin 3, (b μ)^2 : ℝ) : ℂ) • u := by
  funext s
  simp only [fieldFamily, sign_flip, flip_flip, smul_add, smul_smul, Pi.smul_apply]
  simp only [Fin.sum_univ_succ, Complex.ofReal_add, Complex.ofReal_pow]
  match_scalars <;> ring_nf
  simp [Complex.I_sq]
  ring

end Algebra

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Finite spin amplification of the physical photon Hilbert space. -/
abbrev Fiber (N : ℕ) (H : Type*) [NormedAddCommGroup H] :=
  PiLp 2 (fun _ : SpinIndex N => H)

def sigma (n : Fin N) (μ : Fin 3) (u : Fiber N H) : Fiber N H :=
  WithLp.toLp 2 (sigmaFamily n μ u)

def field (n : Fin N) (b : Fin 3 → ℝ) (u : Fiber N H) : Fiber N H :=
  WithLp.toLp 2 (fieldFamily n b u)

@[simp] theorem sigma_apply (n : Fin N) (μ : Fin 3) (u : Fiber N H) (s : SpinIndex N) :
    sigma n μ u s = sigmaFamily n μ u s := rfl

@[simp] theorem field_apply (n : Fin N) (b : Fin 3 → ℝ) (u : Fiber N H) (s : SpinIndex N) :
    field n b u s = fieldFamily n b u s := rfl

theorem fieldFamily_selfadjoint (n : Fin N) (b : Fin 3 → ℝ)
    (u v : SpinIndex N → H) :
    (∑ s, inner ℂ (fieldFamily n b u s) (v s)) =
      ∑ s, inner ℂ (u s) (fieldFamily n b v s) := by
  simp only [fieldFamily, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    simp
  · refine Fintype.sum_equiv (flipEquiv n) _ _ ?_
    intro s
    simp [flipEquiv]

theorem sigmaFamily_selfadjoint (n : Fin N) (μ : Fin 3)
    (u v : SpinIndex N → H) :
    (∑ s, inner ℂ (sigmaFamily n μ u s) (v s)) =
      ∑ s, inner ℂ (u s) (sigmaFamily n μ v s) := by
  have h := fieldFamily_selfadjoint n (fun ν => if ν = μ then 1 else 0) u v
  simpa [fieldFamily_eq_sum, apply_ite] using h

theorem field_selfadjoint (n : Fin N) (b : Fin 3 → ℝ) (u v : Fiber N H) :
    inner ℂ (field n b u) v = inner ℂ u (field n b v) :=
  fieldFamily_selfadjoint n b u v

theorem field_square (n : Fin N) (b : Fin 3 → ℝ) (u : Fiber N H) :
    field n b (field n b u) = ((∑ μ : Fin 3, (b μ)^2 : ℝ) : ℂ) • u := by
  apply PiLp.ext
  intro s
  exact congrFun (fieldFamily_square n b (fun s => u s)) s

/-- Exact classical Zeeman multiplier norm. -/
theorem field_norm_sq (n : Fin N) (b : Fin 3 → ℝ) (u : Fiber N H) :
    ‖field n b u‖^2 = (∑ μ : Fin 3, (b μ)^2) * ‖u‖^2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), field_selfadjoint, field_square,
    inner_smul_right]
  change Complex.re (((∑ μ : Fin 3, (b μ)^2 : ℝ) : ℂ) * inner ℂ u u) = _
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact congrArg (fun r : ℝ => (∑ μ : Fin 3, (b μ)^2) * r)
    (inner_self_eq_norm_sq (𝕜 := ℂ) u)

theorem fieldFamily_sum_norm_sq (n : Fin N) (b : Fin 3 → ℝ) (u : SpinIndex N → H) :
    (∑ s, ‖fieldFamily n b u s‖^2) = (∑ μ : Fin 3, (b μ)^2) * ∑ s, ‖u s‖^2 := by
  have h := field_norm_sq n b (WithLp.toLp 2 u)
  simpa only [PiLp.norm_sq_eq_of_L2, field_apply, PiLp.toLp_apply] using h

end Hilbert

end PfHk.PauliSpin
