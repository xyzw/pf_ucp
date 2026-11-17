import GptLean.SoftPurification
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.L2Space



/-!
Energy estimates for exact soft removal, adapted from
claude_lean/QEDFT/Attainment/SoftRemoval.lean.

The kinetic cancellation is proved in complex Hilbert space. Weighted
Cauchy–Schwarz is proved for genuine integrals. Vacuum tensoring uses the
standard Fock vacuum orthogonality and variance identities as hypotheses.
The new countable sum and scale optimization statements below address the
current manuscript's Steps 5 and 6. Concrete PF form-domain identities and
conditional field moment bounds remain explicit inputs.
-/

namespace GptLean.RemovalEstimates

/-- The unoptimized error, with cluster scale R still free. -/
noncomputable def scaleError (e k R b S : ℝ) : ℝ :=
  (R ^ 2)⁻¹ + e ^ 2 * b ^ 2 + e ^ 2 * k ^ 2 * R ^ 2 * S + e * k * Real.sqrt S

open scoped InnerProductSpace TensorProduct
open Finset



section KeyCancellation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]


theorem key_cancellation {ι : Type*} [Fintype ι] (u w : ι → V) (rem : ℝ) :
    (1 / 2 * ∑ i, ‖u i‖ ^ 2 + ∑ i, RCLike.re ⟪u i, w i⟫_ℂ + rem)
        - 1 / 2 * ∑ i, ‖u i + w i‖ ^ 2
      = rem - 1 / 2 * ∑ i, ‖w i‖ ^ 2 := by
  simp only [norm_add_sq (𝕜 := ℂ), sum_add_distrib, mul_sum]
  simp only [← mul_sum]
  ring


theorem excess_le_rem {ι : Type*} [Fintype ι] (u w : ι → V) (rem : ℝ) :
    (1 / 2 * ∑ i, ‖u i‖ ^ 2 + ∑ i, RCLike.re ⟪u i, w i⟫_ℂ + rem)
        - 1 / 2 * ∑ i, ‖u i + w i‖ ^ 2 ≤ rem := by
  rw [key_cancellation]
  have : 0 ≤ ∑ i, ‖w i‖ ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  linarith

end KeyCancellation



section Elementary


theorem sq_two_mul_add_le (α β x y : ℝ) :
    (2 * α * x + β * y) ^ 2 ≤ 8 * α ^ 2 * x ^ 2 + 2 * β ^ 2 * y ^ 2 := by
  nlinarith [sq_nonneg (2 * α * x - β * y)]


theorem rescaling_identity {κ R : ℝ} (hR : R ≠ 0) (j : ℕ) :
    R ^ (2 * (j : ℤ) - 3) * R ^ (3 : ℤ) * κ ^ (2 * j + 2) = (κ * R) ^ (2 * j) * κ ^ 2 := by
  rw [← zpow_add₀ hR]
  have h : 2 * (j : ℤ) - 3 + 3 = ((2 * j : ℕ) : ℤ) := by push_cast; ring
  rw [h, zpow_natCast, mul_pow, pow_add]
  ring


theorem rescaling_le {κ R : ℝ} (hκR0 : 0 ≤ κ * R) (hκR : κ * R ≤ 1) (j : ℕ) :
    (κ * R) ^ (2 * j) * κ ^ 2 ≤ κ ^ 2 := by
  have h1 : (κ * R) ^ (2 * j) ≤ 1 := pow_le_one₀ hκR0 hκR
  have h2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  nlinarith


theorem sum_sqrt_mul_le {ι : Type*} [Fintype ι] (p B : ι → ℝ) (hp : ∀ l, 0 ≤ p l)
    (hB : ∀ l, 0 ≤ B l) :
    ∑ l, Real.sqrt (p l * B l) ≤ Real.sqrt (∑ l, p l) * Real.sqrt (∑ l, B l) := by
  have h := Real.sum_sqrt_mul_sqrt_le (univ : Finset ι) hp hB
  simpa [Real.sqrt_mul (hp _)] using h

open MeasureTheory in

theorem integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p Z : α → ℝ} (hp : ∀ q, 0 ≤ p q) (hZ : ∀ q, 0 ≤ Z q)
    (hpm : AEStronglyMeasurable p μ) (hZm : AEStronglyMeasurable Z μ)
    (hpi : Integrable p μ) (hpZ : Integrable (fun q => p q * Z q ^ 2) μ) :
    ∫ q, p q * Z q ∂μ ≤ Real.sqrt (∫ q, p q ∂μ) * Real.sqrt (∫ q, p q * Z q ^ 2 ∂μ) := by
  have hf : AEStronglyMeasurable (fun q => Real.sqrt (p q)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hpm
  have hg : AEStronglyMeasurable (fun q => Real.sqrt (p q) * Z q) μ := hf.mul hZm
  have hf2 : MemLp (fun q => Real.sqrt (p q)) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq hf]
    refine hpi.congr (Filter.Eventually.of_forall fun q => ?_)
    simp [Real.sq_sqrt (hp q)]
  have hg2 : MemLp (fun q => Real.sqrt (p q) * Z q) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq hg]
    refine hpZ.congr (Filter.Eventually.of_forall fun q => ?_)
    simp [mul_pow, Real.sq_sqrt (hp q)]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun q => Real.sqrt_nonneg (p q))
    (Filter.Eventually.of_forall fun q => mul_nonneg (Real.sqrt_nonneg _) (hZ q)) hf2 hg2
  simp only [Real.rpow_two, mul_pow, Real.sq_sqrt (hp _), ← Real.sqrt_eq_rpow] at h
  calc ∫ q, p q * Z q ∂μ = ∫ q, Real.sqrt (p q) * (Real.sqrt (p q) * Z q) ∂μ := by
        congr 1; ext q; rw [← mul_assoc, Real.mul_self_sqrt (hp q)]
    _ ≤ _ := h


theorem sum_B_eq {ι : Type*} [Fintype ι] (p E : ι → ℝ) (a b Esoft : ℝ) (hp : ∑ l, p l = 1)
    (hE : ∑ l, E l = Esoft) :
    ∑ l, (a ^ 2 * E l + b ^ 2 * p l) = a ^ 2 * Esoft + b ^ 2 := by
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, hp, hE, mul_one]


theorem sum_sqrt_le_sqrt_S {ι : Type*} [Fintype ι] (p E : ι → ℝ) (a b Esoft : ℝ)
    (hp0 : ∀ l, 0 ≤ p l) (hE0 : ∀ l, 0 ≤ E l) (hp : ∑ l, p l = 1) (hE : ∑ l, E l = Esoft) :
    ∑ l, Real.sqrt (p l * (a ^ 2 * E l + b ^ 2 * p l)) ≤ Real.sqrt (a ^ 2 * Esoft + b ^ 2) := by
  have hB : ∀ l, 0 ≤ a ^ 2 * E l + b ^ 2 * p l := fun l => by
    have := hp0 l; have := hE0 l; positivity
  calc ∑ l, Real.sqrt (p l * (a ^ 2 * E l + b ^ 2 * p l))
      ≤ Real.sqrt (∑ l, p l) * Real.sqrt (∑ l, (a ^ 2 * E l + b ^ 2 * p l)) :=
        sum_sqrt_mul_le p _ hp0 hB
    _ = Real.sqrt (a ^ 2 * Esoft + b ^ 2) := by
        rw [hp, Real.sqrt_one, one_mul, sum_B_eq p E a b Esoft hp hE]


theorem rem_le_of_moments {rem C₀ CZ e R κ M₁ M₂ p B : ℝ} (hC₀ : 0 ≤ C₀) (hCZ : 0 ≤ CZ)
    (he : 0 ≤ e) (hκ : 0 ≤ κ) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hrem : rem ≤ C₀ * (e ^ 2 * R ^ 2 * M₂ + e * M₁))
    (hM₂ : M₂ ≤ CZ * κ ^ 2 * B) (hM₁ : M₁ ≤ Real.sqrt p * Real.sqrt M₂) :
    rem ≤ C₀ * max CZ (Real.sqrt CZ) * e ^ 2 * κ ^ 2 * R ^ 2 * B
        + C₀ * max CZ (Real.sqrt CZ) * e * κ * Real.sqrt (p * B) := by
  have hCmax : CZ ≤ max CZ (Real.sqrt CZ) := le_max_left _ _
  have hCmax' : Real.sqrt CZ ≤ max CZ (Real.sqrt CZ) := le_max_right _ _
  have hsqM₂ : Real.sqrt M₂ ≤ Real.sqrt CZ * κ * Real.sqrt B := by
    calc Real.sqrt M₂ ≤ Real.sqrt (CZ * κ ^ 2 * B) := Real.sqrt_le_sqrt hM₂
      _ = Real.sqrt CZ * κ * Real.sqrt B := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCZ, Real.sqrt_sq hκ]
  have hM₁' : M₁ ≤ Real.sqrt CZ * κ * Real.sqrt (p * B) := by
    calc M₁ ≤ Real.sqrt p * Real.sqrt M₂ := hM₁
      _ ≤ Real.sqrt p * (Real.sqrt CZ * κ * Real.sqrt B) :=
          mul_le_mul_of_nonneg_left hsqM₂ (Real.sqrt_nonneg _)
      _ = Real.sqrt CZ * κ * Real.sqrt (p * B) := by
          rw [Real.sqrt_mul hp]; ring
  have h1 : e ^ 2 * R ^ 2 * M₂ ≤ max CZ (Real.sqrt CZ) * e ^ 2 * κ ^ 2 * R ^ 2 * B := by
    calc e ^ 2 * R ^ 2 * M₂ ≤ e ^ 2 * R ^ 2 * (CZ * κ ^ 2 * B) :=
          mul_le_mul_of_nonneg_left hM₂ (by positivity)
      _ ≤ e ^ 2 * R ^ 2 * (max CZ (Real.sqrt CZ) * κ ^ 2 * B) := by gcongr
      _ = _ := by ring
  have h2 : e * M₁ ≤ max CZ (Real.sqrt CZ) * e * κ * Real.sqrt (p * B) := by
    calc e * M₁ ≤ e * (Real.sqrt CZ * κ * Real.sqrt (p * B)) :=
          mul_le_mul_of_nonneg_left hM₁' he
      _ ≤ e * (max CZ (Real.sqrt CZ) * κ * Real.sqrt (p * B)) := by gcongr
      _ = _ := by ring
  calc rem ≤ C₀ * (e ^ 2 * R ^ 2 * M₂ + e * M₁) := hrem
    _ ≤ C₀ * (max CZ (Real.sqrt CZ) * e ^ 2 * κ ^ 2 * R ^ 2 * B
          + max CZ (Real.sqrt CZ) * e * κ * Real.sqrt (p * B)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC₀
    _ = _ := by ring

end Elementary



section Assembly


theorem output_energy_le {K K' Vc Hhard E T T' C₂ e κ R B p b : ℝ} {N : ℕ}
    (hT : T = K + Vc + Hhard + E)
    (hT' : T' = K' + Vc + Hhard + e ^ 2 * N * b ^ 2 * p / 2)
    (hK' : K' ≤ K + C₂ * e ^ 2 * κ ^ 2 * R ^ 2 * B + C₂ * e * κ * Real.sqrt (p * B)) :
    T' ≤ T - E + C₂ * e ^ 2 * κ ^ 2 * R ^ 2 * B + C₂ * e * κ * Real.sqrt (p * B)
        + e ^ 2 * N * b ^ 2 * p / 2 := by
  subst hT hT'
  linarith


theorem exact_soft_removal_cost {ι : Type*} [Fintype ι] {T₀ Esoft C₁ C₂ e κ R a b : ℝ} {N : ℕ}
    (T T' E p B : ι → ℝ) (he : 0 ≤ e) (hκ : 0 ≤ κ) (hR : 0 < R) (hC₂ : 0 ≤ C₂)
    (hp0 : ∀ l, 0 ≤ p l) (hE0 : ∀ l, 0 ≤ E l) (hB : ∀ l, B l = a ^ 2 * E l + b ^ 2 * p l)
    (hp : ∑ l, p l = 1) (hE : ∑ l, E l = Esoft)
    (hIMS : ∑ l, T l ≤ T₀ + C₁ / R ^ 2)
    (hl : ∀ l, T' l ≤ T l - E l + C₂ * e ^ 2 * κ ^ 2 * R ^ 2 * B l
        + C₂ * e * κ * Real.sqrt (p l * B l) + e ^ 2 * N * b ^ 2 * p l / 2) :
    ∑ l, T' l ≤ T₀ - Esoft + max (max C₁ (N / 2)) C₂
        * scaleError e κ R b (a ^ 2 * Esoft + b ^ 2) := by
  set C := max (max C₁ (N / 2)) C₂ with hC
  have hC₁C : C₁ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hNC : (N : ℝ) / 2 ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC₂C : C₂ ≤ C := le_max_right _ _
  have hS0 : 0 ≤ a ^ 2 * Esoft + b ^ 2 := by
    rw [← hE]; have := sum_nonneg (s := univ) fun l _ => hE0 l; positivity
  have hBsum : ∑ l, B l = a ^ 2 * Esoft + b ^ 2 := by
    simp only [hB]; exact sum_B_eq p E a b Esoft hp hE
  have hsqrt : ∑ l, Real.sqrt (p l * B l) ≤ Real.sqrt (a ^ 2 * Esoft + b ^ 2) := by
    simp only [hB]; exact sum_sqrt_le_sqrt_S p E a b Esoft hp0 hE0 hp hE
  -- sum the per-`l` bounds
  have hsum : ∑ l, T' l ≤ ∑ l, T l - Esoft + C₂ * e ^ 2 * κ ^ 2 * R ^ 2 * (a ^ 2 * Esoft + b ^ 2)
      + C₂ * e * κ * Real.sqrt (a ^ 2 * Esoft + b ^ 2) + e ^ 2 * N * b ^ 2 / 2 := by
    have hterm : ∀ l, T l - E l + C₂ * e ^ 2 * κ ^ 2 * R ^ 2 * B l
        + C₂ * e * κ * Real.sqrt (p l * B l) + e ^ 2 * N * b ^ 2 * p l / 2
        = T l - E l + (C₂ * e ^ 2 * κ ^ 2 * R ^ 2) * B l
          + (C₂ * e * κ) * Real.sqrt (p l * B l) + (e ^ 2 * N * b ^ 2 / 2) * p l := fun l => by
      ring
    calc ∑ l, T' l
        ≤ ∑ l, (T l - E l + C₂ * e ^ 2 * κ ^ 2 * R ^ 2 * B l
            + C₂ * e * κ * Real.sqrt (p l * B l) + e ^ 2 * N * b ^ 2 * p l / 2) :=
          sum_le_sum fun l _ => hl l
      _ = ∑ l, T l - Esoft + C₂ * e ^ 2 * κ ^ 2 * R ^ 2 * (a ^ 2 * Esoft + b ^ 2)
            + C₂ * e * κ * ∑ l, Real.sqrt (p l * B l) + e ^ 2 * N * b ^ 2 / 2 := by
          simp only [hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum, hE, hp, hBsum]
          ring
      _ ≤ _ := by
          have : 0 ≤ C₂ * e * κ := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hsqrt this]
  -- compare with `C · removalError`
  have hR2 : 0 < R ^ 2 := by positivity
  have h1 : C₁ / R ^ 2 ≤ C * (R ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hC₁C (inv_nonneg.mpr hR2.le)
  have h2 : e ^ 2 * N * b ^ 2 / 2 ≤ C * (e ^ 2 * b ^ 2) := by
    have : e ^ 2 * N * b ^ 2 / 2 = (N / 2) * (e ^ 2 * b ^ 2) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hNC (by positivity)
  have h3 : C₂ * e ^ 2 * κ ^ 2 * R ^ 2 * (a ^ 2 * Esoft + b ^ 2)
      ≤ C * (e ^ 2 * κ ^ 2 * R ^ 2 * (a ^ 2 * Esoft + b ^ 2)) := by
    have : C₂ * e ^ 2 * κ ^ 2 * R ^ 2 * (a ^ 2 * Esoft + b ^ 2)
        = C₂ * (e ^ 2 * κ ^ 2 * R ^ 2 * (a ^ 2 * Esoft + b ^ 2)) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hC₂C (by positivity)
  have h4 : C₂ * e * κ * Real.sqrt (a ^ 2 * Esoft + b ^ 2)
      ≤ C * (e * κ * Real.sqrt (a ^ 2 * Esoft + b ^ 2)) := by
    have : C₂ * e * κ * Real.sqrt (a ^ 2 * Esoft + b ^ 2)
        = C₂ * (e * κ * Real.sqrt (a ^ 2 * Esoft + b ^ 2)) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hC₂C (by positivity)
  unfold scaleError
  linarith

end Assembly

section SoftVacuum
variable {V K : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem norm_tmul_vacuum_sub_sq (u ψ : K) {Ω χ : V} (hΩ : ‖Ω‖ = 1) (hχ : ⟪Ω, χ⟫_ℂ = 0)
    (e : ℝ) :
    ‖u ⊗ₜ[ℂ] Ω - (e : ℂ) • (ψ ⊗ₜ[ℂ] χ)‖ ^ 2 = ‖u‖ ^ 2 + e ^ 2 * ‖χ‖ ^ 2 * ‖ψ‖ ^ 2 := by
  rw [TensorProduct.smul_tmul', norm_sub_sq (𝕜 := ℂ), TensorProduct.inner_tmul, hχ, mul_zero,
    map_zero, mul_zero, sub_zero, TensorProduct.norm_tmul, TensorProduct.norm_tmul, hΩ,
    mul_one, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
  ring


theorem soft_vacuum_kinetic_cost {N : ℕ} (u : Fin N → Fin 3 → K) (ψ : K) {Ω : V}
    (χ : Fin 3 → V) (c : Fin 3 → ℝ) (hΩ : ‖Ω‖ = 1) (hχ : ∀ μ, ⟪Ω, χ μ⟫_ℂ = 0)
    (hc : ∀ μ, ‖χ μ‖ ^ 2 = c μ) (e : ℝ) :
    1 / 2 * ∑ i, ∑ μ, ‖u i μ ⊗ₜ[ℂ] Ω - (e : ℂ) • (ψ ⊗ₜ[ℂ] χ μ)‖ ^ 2
      = 1 / 2 * ∑ i, ∑ μ, ‖u i μ‖ ^ 2 + e ^ 2 * N * (∑ μ, c μ) * ‖ψ‖ ^ 2 / 2 := by
  simp only [norm_tmul_vacuum_sub_sq _ _ hΩ (hχ _), hc, sum_add_distrib, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_sum]
  simp only [← mul_sum, ← sum_mul]
  ring


end SoftVacuum

end GptLean.RemovalEstimates
