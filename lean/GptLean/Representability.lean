import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

/-!
Selected representability implications of `qedft.tex`.

The finite Gram identity and coercivity estimates are proved below in genuine
real inner product spaces. The electronic projection theorem is proved from
an abstract partial-trace map and a one-photon purification right inverse.
Those maps are standard Hilbert-space constructions. Their restriction to the
finite-energy Pauli–Fierz domain and the continuum transverse Gram positivity
argument are not constructed here.

The combined-current corollaries explicitly assume the photonic triple
construction. They verify the phase/field algebra only, and do not constitute
a proof of the article's weighted Sobolev construction.
-/

namespace GptLean.Representability

section Projection

variable {P E D J : Type*} [Zero J]

/-- `E` consists of finite-kinetic electronic mixed states and `P` of normalized
finite-energy total pure states. These analytic state types are parameters. -/
structure PurificationInterface (P E D J : Type*) [Zero J] where
  partialTrace : P → E
  onePhotonTag : E → P
  trace_tag : ∀ m, partialTrace (onePhotonTag m) = m
  electronicPair : E → D
  totalElectronicPair : P → D
  pair_trace : ∀ p, totalElectronicPair p = electronicPair (partialTrace p)
  fieldCurrent : P → J
  tag_field_zero : ∀ m, fieldCurrent (onePhotonTag m) = 0

/-- Equation `electronic-projection`, including both set inclusions. -/
theorem electronic_projection (I : PurificationInterface P E D J) :
    Set.range I.totalElectronicPair = Set.range I.electronicPair := by
  ext d
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨I.partialTrace p, (I.pair_trace p).symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨I.onePhotonTag m, ?_⟩
    rw [I.pair_trace, I.trace_tag]

/-- Equation `zero-jph-slice`. The slice fixes the field current, not the
paramagnetic current. -/
theorem zero_field_slice (I : PurificationInterface P E D J) :
    {q : D × J | ∃ p, I.fieldCurrent p = 0 ∧
      q = (I.totalElectronicPair p, I.fieldCurrent p)} =
    {q : D × J | q.1 ∈ Set.range I.electronicPair ∧ q.2 = 0} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨I.partialTrace p, (I.pair_trace p).symm⟩, hp⟩
  · rintro ⟨⟨m, hm⟩, hj⟩
    refine ⟨I.onePhotonTag m, I.tag_field_zero m, ?_⟩
    apply Prod.ext
    · simp only [I.pair_trace, I.trace_tag]
      exact hm.symm
    · simpa only [I.tag_field_zero] using hj

end Projection

section Gram

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

open scoped InnerProductSpace

/-- The Gram quadratic form is a norm square. The factor 2 in the article's
kernel can be applied afterwards and does not affect positivity. -/
theorem gram_quadratic_form (g : ι → H) (c : ι → ℝ) :
    (∑ i, ∑ j, c i * c j * ⟪g i, g j⟫_ℝ) = ‖∑ i, c i • g i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (g j) (g i)]
  ring

/-- Positivity is strict exactly when no nonzero coefficient vector is killed.
For the continuum transverse kernels, establishing this injectivity uses the
measure-zero line argument in `photonic-Gram-positivity`. -/
theorem gram_strictly_positive (g : ι → H)
    (hinj : Function.Injective (fun c : ι → ℝ => ∑ i, c i • g i))
    (c : ι → ℝ) (hc : c ≠ 0) :
    0 < ∑ i, ∑ j, c i * c j * ⟪g i, g j⟫_ℝ := by
  rw [gram_quadratic_form]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hzero
  apply hc
  apply hinj
  simpa only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] using hzero

omit [InnerProductSpace ℝ H] in
/-- The article's kernel quadratic form `2 * ‖integral ...‖²` is nonnegative. -/
theorem kernel_quadratic_nonnegative (z : H) : 0 ≤ 2 * ‖z‖ ^ 2 := by positivity

end Gram

section FieldEquation

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The passage from `M ≥ λ I` and `Kρ ≥ 0` to `T ≥ λ I` in Step 3.
The operators need not commute. -/
theorem displacement_coercive (M K : H → H) (ell α : ℝ)
    (hM : ∀ u, ell * ‖u‖ ^ 2 ≤ ⟪u, M u⟫_ℝ)
    (hK : ∀ u, 0 ≤ ⟪u, K u⟫_ℝ) (hα : 0 ≤ α) (u : H) :
    ell * ‖u‖ ^ 2 ≤ ⟪u, M u + α • K u⟫_ℝ := by
  rw [inner_add_right, real_inner_smul_right]
  exact (hM u).trans (le_add_of_nonneg_right (mul_nonneg hα (hK u)))

theorem particle_coefficient_nonnegative (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ ((N : ℝ) - 1) / (N : ℝ) := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact div_nonneg (sub_nonneg.mpr hn) (by linarith)

/-- The quantitative estimate in `photonic-field-equation` for any solution.
Existence of a solution from bounded self-adjoint coercivity is a standard
functional-analysis input not reproved here. -/
theorem displacement_solution_bound (T : H → H) (ell : ℝ) (hell : 0 < ell)
    (hT : ∀ u, ell * ‖u‖ ^ 2 ≤ ⟪u, T u⟫_ℝ)
    (u a : H) (heq : T u = a) : ‖u‖ ≤ ell⁻¹ * ‖a‖ := by
  have h := hT u
  rw [heq] at h
  have hcs := real_inner_le_norm u a
  have hu : 0 ≤ ‖u‖ := norm_nonneg u
  by_cases hzero : ‖u‖ = 0
  · rw [hzero]
    exact mul_nonneg (inv_nonneg.mpr hell.le) (norm_nonneg a)
  · have hup : 0 < ‖u‖ := lt_of_le_of_ne hu (Ne.symm hzero)
    have hlin : ell * ‖u‖ ≤ ‖a‖ := by nlinarith
    have hdiv : ‖u‖ ≤ ‖a‖ / ell :=
      (le_div_iff₀ hell).mpr (by simpa only [mul_comm] using hlin)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv

end FieldEquation

section CombinedCurrent

variable {X P W : Type*} [AddCommGroup W] [Module ℝ W]

/-- A supplied construction of the photonic triple, restricted to admissible
profiles. The weighted Sobolev conditions are encoded by `admissible`. -/
def TripleConstruction (ρ : X → ℝ) (e : ℝ)
    (density : P → X → ℝ) (jp jph : P → X → W)
    (admissible : (X → W) → (X → W) → (X → W) → Prop) : Prop :=
  ∀ a b phase, admissible a b phase → ∃ p,
    density p = ρ ∧
    (∀ x, jp p x = ρ x • (phase x + b x)) ∧
    (∀ x, jph p x = (-e * ρ x) • a x)

/-- A freely chosen field profile can be compensated in the paramagnetic velocity.
This identity includes zero coupling and does not divide by the density. -/
theorem compensated_velocity (ρ e : ℝ) (v a : W) :
    ρ • (v + e • a) + (-e * ρ) • a = ρ • v := by
  rw [smul_add, smul_smul]
  have hc : -e * ρ = -(ρ * e) := by ring
  rw [hc, neg_smul]
  abel

/-- The field-only choice in `cor-photonic-combined-class`.
This establishes the exact sign and the need for nonzero coupling. -/
theorem field_only_velocity (ρ e : ℝ) (he : e ≠ 0) (v : W) :
    (-e * ρ) • ((-e⁻¹) • v) = ρ • v := by
  rw [smul_smul]
  congr 1
  field_simp

/-- The phase plus Sobolev-velocity corollary, conditional on admissibility
of the scaled field profile and on the actual triple construction. -/
theorem phase_plus_velocity_representable
    (ρ : X → ℝ) (e : ℝ) (he : e ≠ 0)
    (density : P → X → ℝ) (jp jph : P → X → W)
    (admissible : (X → W) → (X → W) → (X → W) → Prop)
    (build : TripleConstruction ρ e density jp jph admissible)
    (phase w : X → W)
    (hadm : admissible (fun x => (-e⁻¹) • w x) (fun _ => 0) phase) :
    ∃ p, density p = ρ ∧ ∀ x, jp p x + jph p x = ρ x • (phase x + w x) := by
  obtain ⟨p, hp, hjp, hjph⟩ := build _ _ _ hadm
  refine ⟨p, hp, fun x => ?_⟩
  rw [hjp, hjph, add_zero, field_only_velocity _ _ he, smul_add]

end CombinedCurrent

end GptLean.Representability
