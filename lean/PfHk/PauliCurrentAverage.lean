import GptLean.PhysicalPairSpace

/-! Finite averaging of actual L1 density components. -/

noncomputable section
namespace PfHk.PauliCurrentAverage
open MeasureTheory GptLean GptLean.PhysicalPairSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
attribute [local irreducible] densityL1

theorem density_of_ae {K : ℕ} (hK : 0 < K)
    (P : Fin K → Pair)
    (ρ : Lp ℝ 1 (volume : Measure PhysicalPairSpace.Position))
    (f : Fin K → PhysicalPairSpace.Position → ℝ)
    (hp : ∀ i, (densityL1 (P i) : PhysicalPairSpace.Position → ℝ) =ᵐ[volume]
      fun x => (K : ℝ) * f i x)
    (hρ : (ρ : PhysicalPairSpace.Position → ℝ) =ᵐ[volume] fun x => ∑ i, f i x) :
    densityL1 ((K : ℝ)⁻¹ • ∑ i, P i) = ρ := by
  have hmap : densityL1 ((K : ℝ)⁻¹ • ∑ i, P i) =
      (K : ℝ)⁻¹ • ∑ i, densityL1 (P i) :=
    (map_smul densityL1 (K : ℝ)⁻¹ (∑ i, P i)).trans
      (congrArg (fun r : Lp ℝ 1 (volume : Measure PhysicalPairSpace.Position) => (K : ℝ)⁻¹ • r)
        (map_sum densityL1 P Finset.univ))
  refine hmap.trans ?_
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (K : ℝ)⁻¹ (∑ i, densityL1 (P i)),
    Lp.coeFn_finsetSum Finset.univ (fun i => densityL1 (P i)), ae_all_iff.mpr hp, hρ]
    with x hsm hsum hpart hrho
  rw [hsm]
  simp only [Pi.smul_apply]
  rw [hsum, hrho]
  simp only [Finset.sum_apply, smul_eq_mul]
  simp_rw [hpart]
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hK.ne'), one_mul]

end PfHk.PauliCurrentAverage
