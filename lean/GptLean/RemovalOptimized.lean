import GptLean.SoftRemoval

/-! The optimizing scale preserves every property proved for the common
free-scale state, including zero soft energy and fermionic support. -/

namespace GptLean.SoftRemoval

open RemovalAssembly

theorem optimized_output_with_property
    {M Pair Marginal : Type*} {B : DFT.StateModel M Pair} (m : M)
    (marginal : M → Marginal) (target : Marginal) (property : M → Prop)
    {Esoft C e k a b : ℝ}
    (hC : 0 ≤ C) (he : 0 ≤ e) (hk : 0 < k) (hk1 : k ≤ 1) (hE : 0 ≤ Esoft)
    (outputs : ∀ R, 1 ≤ R → k * R ≤ 1 →
      {out : LocalizedOutput B m marginal target Esoft C e k R a b // property out.state}) :
    ∃ r, B.density r = B.density m ∧ marginal r = target ∧ property r ∧
      B.energy r ≤ B.energy m - Esoft +
        (3 * C) * SoftPurification.removalError e k a b Esoft := by
  obtain ⟨R, hR, hkR, hcost⟩ := exists_optimized_scale (a := a) (b := b) he hk hk1 hE
  let out := outputs R hR hkR
  refine ⟨out.val.state, out.val.pair_eq, out.val.marginal_eq, out.property, ?_⟩
  have h := out.val.energy_bound hC he hk.le
  have hmul := mul_le_mul_of_nonneg_left hcost hC
  nlinarith

end GptLean.SoftRemoval
