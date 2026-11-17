import PfHk.CarlemanWeights
import Mathlib.Order.Filter.Finite

/-! Common radius and parameter choices for finitely many external
perturbation terms. These are consequences of the proved logarithmic
weight asymptotics, with no physical estimate among the hypotheses. -/

noncomputable section
namespace PfHk.PerturbationSmallness

open Filter Set PfHk.CarlemanWeights
open scoped Topology

set_option Elab.async false
set_option maxHeartbeats 20000

variable {J : Type*} [Fintype J]

/-- Every positive radius exponent can be controlled on the same smaller
ball. The conclusion includes all smaller outer radii. -/
theorem exists_common_radius (α : ℝ) (a : J → ℝ) (ha : ∀ j, 0 < a j)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ R ∧ r₀ < Real.exp (-2) ∧
      ∀ j, ∀ r : ℝ, 0 < r → r ≤ r₀ →
        r ^ a j / beta α (-Real.log r) < ε := by
  have hevent : ∀ᶠ t : ℝ in atTop, ∀ j, cylinderRatio α (a j) t < ε :=
    Filter.eventually_all.mpr fun j =>
      (cylinderRatio_tendsto_zero α (ha j)).eventually_lt_const hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  let t₀ : ℝ := max T 3
  let r₀ : ℝ := min R (Real.exp (-t₀))
  have hr₀ : 0 < r₀ := lt_min hR (Real.exp_pos _)
  refine ⟨r₀, hr₀, min_le_left _ _, ?_, ?_⟩
  · apply (min_le_right R (Real.exp (-t₀))).trans_lt
    apply Real.exp_lt_exp.mpr
    have ht : 3 ≤ t₀ := le_max_right _ _
    linarith
  · intro j r hr hrr₀
    have hrupper : r ≤ Real.exp (-t₀) := hrr₀.trans (min_le_right _ _)
    have hlog : Real.log r ≤ -t₀ := by
      simpa only [Real.log_exp] using Real.log_le_log hr hrupper
    have hge : T ≤ -Real.log r := by
      have ht : T ≤ t₀ := le_max_left _ _
      linarith
    simpa only [cylinderRatio, neg_neg, Real.exp_log hr] using hT _ hge j

theorem radiusSup_le_of_bound {α a R K : ℝ} (hR : 0 < R)
    (hbound : ∀ r : ℝ, 0 < r → r ≤ R → r ^ a / beta α (-Real.log r) ≤ K) :
    radiusSup α a R ≤ K := by
  apply csSup_le
  · exact ⟨_, ⟨R, ⟨hR, le_rfl⟩, rfl⟩⟩
  · rintro y ⟨r, hr, rfl⟩
    exact hbound r hr.1 hr.2

theorem ratio_le_radiusSup {α a R K r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hbound : ∀ t : ℝ, 0 < t → t ≤ R → t ^ a / beta α (-Real.log t) ≤ K) :
    r ^ a / beta α (-Real.log r) ≤ radiusSup α a R := by
  apply le_csSup
  · refine ⟨K, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    exact hbound t ht.1 ht.2
  · exact ⟨r, ⟨hr, hrR⟩, rfl⟩

theorem radiusSup_nonneg_of_bound {α a R K : ℝ} (hα : 0 < α) (hR : 0 < R)
    (hsmall : R < Real.exp (-2))
    (hbound : ∀ r : ℝ, 0 < r → r ≤ R → r ^ a / beta α (-Real.log r) ≤ K) :
    0 ≤ radiusSup α a R := by
  have hlog : 0 < -Real.log R := by
    have h := Real.log_lt_log hR hsmall
    rw [Real.log_exp] at h
    linarith
  exact (div_nonneg (Real.rpow_nonneg hR.le _) (beta_pos hα hlog).le).trans
    (ratio_le_radiusSup hR le_rfl hbound)

/-- A common small radius controls any finite sum of the perturbation
coefficients. Parameter powers of nonpositive order are at most one for
every parameter above one. The constants may be arbitrarily large. -/
theorem exists_small_coefficient_with_ratios (α : ℝ) (hα : 0 < α)
    (a b K : J → ℝ) (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 ≤ b j)
    (hK : ∀ j, 0 ≤ K j) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ R ∧ r₀ < Real.exp (-2) ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        (∀ j, 0 ≤ radiusSup α (a j) r) ∧
        (∀ j, ∀ t : ℝ, 0 < t → t ≤ r →
          t ^ a j / beta α (-Real.log t) ≤ radiusSup α (a j) r) ∧
        ∀ τ : ℝ, 1 ≤ τ →
          (∑ j, K j * radiusSup α (a j) r * τ ^ (-b j)) ≤ ε := by
  let M : ℝ := ∑ j, K j
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => hK j
  let δ : ℝ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨r₀, hr₀, hrR, hrsmall, hratios⟩ := exists_common_radius α a ha hR hδ
  refine ⟨r₀, hr₀, hrR, hrsmall, ?_⟩
  intro r hr hrr₀
  have hbound : ∀ j, ∀ t : ℝ, 0 < t → t ≤ r →
      t ^ a j / beta α (-Real.log t) ≤ δ := by
    intro j t ht htr
    exact (hratios j t ht (htr.trans hrr₀)).le
  have hσ : ∀ j, 0 ≤ radiusSup α (a j) r := fun j =>
    radiusSup_nonneg_of_bound hα hr (hrr₀.trans_lt hrsmall) (hbound j)
  refine ⟨hσ, (fun j t ht htr => ratio_le_radiusSup ht htr (hbound j)), ?_⟩
  intro τ hτ
  have hsum : (∑ j, K j * radiusSup α (a j) r * τ ^ (-b j)) ≤ M * δ := by
    calc
      _ ≤ ∑ j, K j * δ := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ K j * radiusSup α (a j) r * 1 :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_one_of_one_le_of_nonpos hτ (neg_nonpos.mpr (hb j)))
              (mul_nonneg (hK j) (hσ j))
          _ ≤ K j * δ := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left (radiusSup_le_of_bound hr (hbound j)) (hK j)
      _ = M * δ := by rw [Finset.sum_mul]
  apply hsum.trans
  dsimp [δ]
  have hden : 0 < M + 1 := by linarith
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  nlinarith

theorem exists_small_coefficient (α : ℝ) (hα : 0 < α)
    (a b K : J → ℝ) (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 ≤ b j)
    (hK : ∀ j, 0 ≤ K j) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ R ∧ r₀ < Real.exp (-2) ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        (∀ j, 0 ≤ radiusSup α (a j) r) ∧
        ∀ τ : ℝ, 1 ≤ τ →
          (∑ j, K j * radiusSup α (a j) r * τ ^ (-b j)) ≤ ε := by
  obtain ⟨r₀, hpos, hle, hsmall, h⟩ :=
    exists_small_coefficient_with_ratios α hα a b K ha hb hK hR hε
  exact ⟨r₀, hpos, hle, hsmall, fun r hr hrr₀ => ⟨(h r hr hrr₀).1, (h r hr hrr₀).2.2⟩⟩

end PfHk.PerturbationSmallness
