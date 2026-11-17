import GptLean.RemovalSourceConditioned

/-!
The actual conditioned source has the original total soft energy and
satisfies the summed IMS estimate. These are consequences of localization
and unitarity, before the repair channel is constructed.
-/

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open MeasureTheory ElectronicLocalization

variable {Q X J H K Hr Kr Hs : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X} [SFinite μ] [SFinite ν] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

variable
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (Ur : Lp Hr 2 ν ≃ₗᵢ[ℂ] Lp Kr 2 (μ.prod ν))
    (f : ℕ → X → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (f a)))
    (hd : ∀ a, Differentiable ℝ (f a)) (hpos : ∀ a x, 0 ≤ f a x)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν)
    (ψ : ℕ → Lp H 2 ν) (dψ : ℕ → J → Lp H 2 ν)
    (rest : ℕ → Lp Hr 2 ν) (soft : ℕ → Lp Hs 2 ν) (v : J → X)
    (hdf : ∀ a j, AEStronglyMeasurable (fun x => fderiv ℝ (f a) x (v j)) ν)
    (C : J → ℝ) (hmetric : ∀ j x, (∑' a, fderiv ℝ (f a) x (v j) ^ 2) ≤ C j)
    (hmass : HasSum (fun n => ‖ψ n‖ ^ 2) 1)
    (hkinetic : ∀ j, Summable (fun n => ‖dψ n j‖ ^ 2))
    (hrest : Summable (fun n => ‖rest n‖ ^ 2))
    (hsoft : Summable (fun n => ‖soft n‖ ^ 2))

local notation "S" => localizedConditionedSource U Ur f hloc hd hpos hpart hf ψ dψ rest soft v
  hdf C hmetric hmass hkinetic hrest hsoft

theorem localizedConditionedSource_soft_hasSum {Esoft : ℝ}
    (hsource : HasSum (fun n => ‖soft n‖ ^ 2) Esoft) : HasSum (S).soft Esoft := by
  change HasSum
    (fun i => ‖localizedVector f hpart hf (soft (Nat.unpair i).1) (Nat.unpair i).2‖ ^ 2) Esoft
  simpa only [Repair.flattenVectors] using
    Repair.flattenVectors_mass (fun n => localizedVector_mass f hpart hf (soft n)) hsource

theorem localizedConditionedSource_rest_hasSum {Erest : ℝ}
    (hsource : HasSum (fun n => ‖rest n‖ ^ 2) Erest) :
    HasSum (fun i => ‖(S).rest i‖ ^ 2) Erest := by
  change HasSum
    (fun i => ‖Ur (localizedVector f hpart hf (rest (Nat.unpair i).1) (Nat.unpair i).2)‖ ^ 2) Erest
  simpa only [Ur.norm_map, Repair.flattenVectors] using
    Repair.flattenVectors_mass (fun n => localizedVector_mass f hpart hf (rest n)) hsource

theorem localizedConditionedSource_kinetic_bound :
    (∑' i, (1 / 2 : ℝ) * ∑ j, ‖(S).covariant i j‖ ^ 2) ≤
      (1 / 2 : ℝ) * ∑ j, ((∑' n, ‖dψ n j‖ ^ 2) + C j) := by
  classical
  have hi (n : ℕ) (j : J) : Integrable (fun x => ‖dψ n j x‖ ^ 2 +
      (∑' a, fderiv ℝ (f a) x (v j) ^ 2) * ‖ψ n x‖ ^ 2) ν :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp (dψ n j)).1).mp (Lp.memLp (dψ n j))).add
      (localizedSourceMetric_integrable f (v j) (fun a => hdf a j) (ψ n) (hmetric j))
  let hm (n : ℕ) (j : J) (a : ℕ) :
      MemLp (localizedDerivative f (dψ n j) (ψ n) (v j) a) 2 ν :=
    localizedDerivative_memLp f hloc hd hpos hpart hf (ψ n) (dψ n j) (v j)
      (fun a => hdf a j) (hi n j) a
  have hs (j : J) : Summable (fun i => ‖localizedDerivativeVector f (ψ (Nat.unpair i).1)
      (dψ (Nat.unpair i).1 j) (v j) (fun a => hm (Nat.unpair i).1 j a) (Nat.unpair i).2‖ ^ 2) := unpair_summable
    (g := fun p : ℕ × ℕ =>
      ‖localizedDerivativeVector f (ψ p.1) (dψ p.1 j) (v j) (fun a => hm p.1 j a) p.2‖ ^ 2)
    (localizedDerivativeVector_summable f hloc hd hpos hpart hf ψ (fun n => dψ n j)
      (v j) (fun a => hdf a j) (fun n => hi n j) (fun n a => hm n j a)
      (hmetric j) hmass.summable (hkinetic j))
  change (∑' i, (1 / 2 : ℝ) * ∑ j,
      ‖U (localizedDerivativeVector f (ψ (Nat.unpair i).1) (dψ (Nat.unpair i).1 j)
        (v j) (fun a => hm (Nat.unpair i).1 j a) (Nat.unpair i).2)‖ ^ 2) ≤ _
  simp only [U.norm_map]
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun j _ => hs j)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro j _
  calc
    _ = ∑' p : ℕ × ℕ,
        ‖localizedDerivativeVector f (ψ p.1) (dψ p.1 j) (v j) (fun a => hm p.1 j a) p.2‖ ^ 2 :=
      Nat.pairEquiv.symm.tsum_eq _
    _ ≤ (∑' n, ‖dψ n j‖ ^ 2) + C j :=
      localizedDerivativeVector_tsum_bound f hloc hd hpos hpart hf ψ (fun n => dψ n j)
        (v j) (fun a => hdf a j) (fun n a => hm n j a) (hmetric j) hmass (hkinetic j)

/-- The source-energy sum is bounded by the original spectral kinetic,
hard and soft form energies plus the localization metric cost. -/
theorem localizedConditionedSource_input_bound :
    (∑' i, (S).input i) ≤
      ((1 / 2 : ℝ) * ∑ j, ∑' n, ‖dψ n j‖ ^ 2) +
        (∑' n, ‖rest n‖ ^ 2) + (∑' n, ‖soft n‖ ^ 2) + (1 / 2 : ℝ) * ∑ j, C j := by
  change tsum (fun i => ((1 / 2 : ℝ) * ∑ j, ‖(S).covariant i j‖ ^ 2) +
    ‖(S).rest i‖ ^ 2 + (S).soft i) ≤ _
  rw [((S).kinetic_summable.add (S).rest_summable).tsum_add (S).soft_summable,
    (S).kinetic_summable.tsum_add (S).rest_summable]
  have hr := localizedConditionedSource_rest_hasSum U Ur f hloc hd hpos hpart hf
    ψ dψ rest soft v hdf C hmetric hmass hkinetic hrest hsoft hrest.hasSum
  have hs := localizedConditionedSource_soft_hasSum U Ur f hloc hd hpos hpart hf
    ψ dψ rest soft v hdf C hmetric hmass hkinetic hrest hsoft hsoft.hasSum
  rw [hr.tsum_eq, hs.tsum_eq]
  have hk := localizedConditionedSource_kinetic_bound U Ur f hloc hd hpos hpart hf
    ψ dψ rest soft v hdf C hmetric hmass hkinetic hrest hsoft
  simp only [Finset.sum_add_distrib] at hk
  linarith

end GptLean.RemovalSource
