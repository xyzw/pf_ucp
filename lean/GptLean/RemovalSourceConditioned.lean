import GptLean.RemovalSourceProduct
import GptLean.RemovalConditioned

/-!
The conditioned source is constructed from localized original spectral
vectors and their WIS images. All three energy series and normalization
are proved from original spectral summability and the spatial IMS bound.
No conditional or localized source series is a constructor input.
-/

noncomputable section

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open MeasureTheory Filter ElectronicLocalization

theorem unpair_summable {g : ℕ × ℕ → ℝ} (h : Summable g) :
    Summable (fun i => g (Nat.unpair i)) := by
  change Summable (g ∘ Nat.pairEquiv.symm)
  exact Nat.pairEquiv.symm.summable_iff.mpr h

section ConditionedConstruction

variable {Q X J H K Hr Kr Hs : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X} [SFinite μ] [SFinite ν] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

theorem localizedSourceMetric_integrable
    (f : ℕ → X → ℝ) (v : X)
    (hdf : ∀ a, AEStronglyMeasurable (fun x => fderiv ℝ (f a) x v) ν)
    (ψ : Lp H 2 ν) {C : ℝ} (hmetric : ∀ x, (∑' a, fderiv ℝ (f a) x v ^ 2) ≤ C) :
    Integrable (fun x => (∑' a, fderiv ℝ (f a) x v ^ 2) * ‖ψ x‖ ^ 2) ν := by
  have hψ := (memLp_two_iff_integrable_sq_norm (Lp.memLp ψ).1).mp (Lp.memLp ψ)
  have hm : AEStronglyMeasurable (fun x => ∑' a, fderiv ℝ (f a) x v ^ 2) ν :=
    AEStronglyMeasurable.tsum (fun a => (hdf a).pow 2)
  apply (hψ.const_mul C).mono' (hm.mul hψ.aestronglyMeasurable)
  filter_upwards with x
  change ‖(∑' a, fderiv ℝ (f a) x v ^ 2) * ‖ψ x‖ ^ 2‖ ≤ C * ‖ψ x‖ ^ 2
  rw [Real.norm_of_nonneg (mul_nonneg (tsum_nonneg (fun _ => sq_nonneg _)) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hmetric x) (sq_nonneg _)

theorem localizedDerivativeVector_tsum_bound
    (f : ℕ → X → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (f a)))
    (hd : ∀ a, Differentiable ℝ (f a)) (hpos : ∀ a x, 0 ≤ f a x)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν)
    (ψ dψ : ℕ → Lp H 2 ν) (v : X)
    (hdf : ∀ a, AEStronglyMeasurable (fun x => fderiv ℝ (f a) x v) ν)
    (hmem : ∀ n a, MemLp (localizedDerivative f (dψ n) (ψ n) v a) 2 ν)
    {C : ℝ} (hmetric : ∀ x, (∑' a, fderiv ℝ (f a) x v ^ 2) ≤ C)
    (hmass : HasSum (fun n => ‖ψ n‖ ^ 2) 1)
    (hkinetic : Summable (fun n => ‖dψ n‖ ^ 2)) :
    (∑' p : ℕ × ℕ, ‖localizedDerivativeVector f (ψ p.1) (dψ p.1) v (hmem p.1) p.2‖ ^ 2) ≤
      (∑' n, ‖dψ n‖ ^ 2) + C := by
  have hm (n : ℕ) := localizedSourceMetric_integrable f v hdf (ψ n) hmetric
  have hi (n : ℕ) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp (dψ n)).1).mp (Lp.memLp (dψ n))).add (hm n)
  have hs := localizedDerivativeVector_summable f hloc hd hpos hpart hf ψ dψ v hdf
    hi hmem hmetric hmass.summable hkinetic
  have hr (n : ℕ) := localizedDerivativeVector_ims f hloc hd hpos hpart hf
    (ψ n) (dψ n) v hdf (hi n) (hmem n)
  rw [hs.tsum_prod' (fun n => (hr n).summable)]
  have hle (n : ℕ) :
      (∑' a, ‖localizedDerivativeVector f (ψ n) (dψ n) v (hmem n) a‖ ^ 2) ≤
      ‖dψ n‖ ^ 2 + C * ‖ψ n‖ ^ 2 := by
    rw [(hr n).tsum_eq]
    have hψ := (memLp_two_iff_integrable_sq_norm (Lp.memLp (ψ n)).1).mp (Lp.memLp (ψ n))
    have hdψ := (memLp_two_iff_integrable_sq_norm (Lp.memLp (dψ n)).1).mp (Lp.memLp (dψ n))
    have hb := integral_mono_ae (hi n) (hdψ.add (hψ.const_mul C))
      (Filter.Eventually.of_forall (fun x => add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (hmetric x) (sq_nonneg _))))
    change (∫ x, ‖dψ n x‖ ^ 2 + (∑' a, fderiv ℝ (f a) x v ^ 2) * ‖ψ n x‖ ^ 2 ∂ν) ≤
      (∫ x, ‖dψ n x‖ ^ 2 + C * ‖ψ n x‖ ^ 2 ∂ν) at hb
    simpa only [integral_add hdψ (hψ.const_mul C), integral_const_mul, ← lp_norm_sq] using hb
  have hb := Summable.tsum_le_tsum hle hs.prod (hkinetic.add (hmass.summable.mul_left C))
  simpa only [hkinetic.tsum_add (hmass.summable.mul_left C), tsum_mul_left, hmass.tsum_eq,
    mul_one] using hb

/-- An actual localized and conditioned source, including its covariant
derivatives and hard and soft form vectors. The soft form vectors need
only their scalar norm because they are discarded by vacuum preparation. -/
def localizedConditionedSource
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
    (hsoft : Summable (fun n => ‖soft n‖ ^ 2)) :
    RemovalEnergy.ConditionedSource μ ν J K Kr := by
  have hint (n : ℕ) (j : J) : Integrable (fun x => ‖dψ n j x‖ ^ 2 +
      (∑' a, fderiv ℝ (f a) x (v j) ^ 2) * ‖ψ n x‖ ^ 2) ν :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp (dψ n j)).1).mp (Lp.memLp (dψ n j))).add
      (localizedSourceMetric_integrable f (v j) (fun a => hdf a j) (ψ n) (hmetric j))
  let hm (n : ℕ) (j : J) (a : ℕ) :
      MemLp (localizedDerivative f (dψ n j) (ψ n) (v j) a) 2 ν :=
    localizedDerivative_memLp f hloc hd hpos hpart hf (ψ n) (dψ n j) (v j)
      (fun a => hdf a j) (hint n j) a
  refine {
    source := fun i => U (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2)
    covariant := fun i j => U (localizedDerivativeVector f (ψ (Nat.unpair i).1)
      (dψ (Nat.unpair i).1 j) (v j) (fun a => hm (Nat.unpair i).1 j a) (Nat.unpair i).2)
    rest := fun i => Ur (localizedVector f hpart hf (rest (Nat.unpair i).1) (Nat.unpair i).2)
    normalized := ?_
    kinetic_summable := ?_
    rest_summable := ?_
    soft := fun i => ‖localizedVector f hpart hf (soft (Nat.unpair i).1) (Nat.unpair i).2‖ ^ 2
    soft_nonneg := fun _ => sq_nonneg _
    soft_summable := ?_
  }
  · simpa only [U.norm_map, Repair.flattenVectors] using
      Repair.flattenVectors_mass (fun n => localizedVector_mass f hpart hf (ψ n)) hmass
  · have hs (j : J) : Summable (fun i => ‖localizedDerivativeVector f (ψ (Nat.unpair i).1)
        (dψ (Nat.unpair i).1 j) (v j) (fun a => hm (Nat.unpair i).1 j a) (Nat.unpair i).2‖ ^ 2) := unpair_summable
      (g := fun p : ℕ × ℕ =>
        ‖localizedDerivativeVector f (ψ p.1) (dψ p.1 j) (v j) (fun a => hm p.1 j a) p.2‖ ^ 2)
      (localizedDerivativeVector_summable f hloc hd hpos hpart hf ψ (fun n => dψ n j)
        (v j) (fun a => hdf a j) (fun n => hint n j) (fun n a => hm n j a)
        (hmetric j) hmass.summable (hkinetic j))
    simpa only [U.norm_map] using
      (summable_sum (s := Finset.univ) (fun j _ => hs j)).mul_left (1 / 2 : ℝ)
  · simpa only [Ur.norm_map] using
      unpair_summable
        (g := fun p : ℕ × ℕ => ‖localizedVector f hpart hf (rest p.1) p.2‖ ^ 2)
        (localizedVector_mass_prod f hpart hf rest hrest)
  · exact unpair_summable
      (g := fun p : ℕ × ℕ => ‖localizedVector f hpart hf (soft p.1) p.2‖ ^ 2)
      (localizedVector_mass_prod f hpart hf soft hsoft)

end ConditionedConstruction
end GptLean.RemovalSource
