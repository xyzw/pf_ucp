import PfHk.PerturbationSmallness
import PfHk.WeightedDyadicBounds

/-! One radius controls the classical dyadic and quantum mass ratios.
The bounds hold on the whole punctured ball and for every smaller outer
radius, so the subsequent parameter choice is uniform. -/

noncomputable section
namespace PfHk.PauliCarlemanRadii

open PfHk.CarlemanWeights PfHk.SmoothDyadicCutoffs

set_option Elab.async false
set_option maxHeartbeats 20000

variable {J : Type*} [Fintype J]

theorem exists_common_radius (α : ℝ) (a : J → ℝ) (ha : ∀ j, 0 < a j)
    {Rcap : ℝ} (hRcap : 0 < Rcap) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ Rcap ∧ 2 * r₀ ≤ Real.exp (-2) ∧
      r₀ < Real.exp (-2) ∧
      (∀ j, ∀ r : ℝ, 0 < r → r ≤ r₀ →
        r ^ a j / beta α (-Real.log r) ≤ 1) ∧
      ∀ j, ∀ R : ℝ, 0 < R → R ≤ r₀ → ∀ k : ℕ,
        radius R k ^ a j / dyadicBeta α R k ≤ 1 := by
  let cap : ℝ := min Rcap (Real.exp (-2) / 2)
  have hcap : 0 < cap := lt_min hRcap (div_pos (Real.exp_pos _) (by norm_num))
  obtain ⟨r₀, hr₀, hrcap, hrsmall, hbound⟩ :=
    PerturbationSmallness.exists_common_radius α a ha hcap (by norm_num : (0 : ℝ) < 1)
  have hrR : r₀ ≤ Rcap := hrcap.trans (min_le_left _ _)
  have hrhalf : r₀ ≤ Real.exp (-2) / 2 := hrcap.trans (min_le_right _ _)
  refine ⟨r₀, hr₀, hrR, by linarith only [hrhalf], hrsmall,
    fun j r hr hrr => (hbound j r hr hrr).le, ?_⟩
  intro j R hR hRr k
  exact (hbound j (radius R k) (radius_pos hR k)
    ((radius_le hR.le k).trans hRr)).le

end PfHk.PauliCarlemanRadii
