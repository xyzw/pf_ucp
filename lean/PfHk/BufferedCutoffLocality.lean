import PfHk.PhysicalCutoffLocality
import PfHk.SmoothCutoffGeometry

/-! A buffered scalar cutoff is exactly one, with both derivative orders
zero, on every L2 vector supported in its inner ball. -/

noncomputable section
namespace PfHk.BufferedCutoffLocality

open MeasureTheory GptLean GptLean.PhysicalPFReference
  GptLean.ElectronicH1Space GptLean.ElectronicH1Multiplier
  PfHk.SmoothCutoffBounds PfHk.PhysicalCutoffCommutator

set_option Elab.async false
set_option maxHeartbeats 30000

variable {I H : Type} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem scalar_map_eq (u v : L2 H I) (b : Position I → ℝ)
    (hrep : (v : Position I → H) =ᵐ[volume] fun x => b x • u x)
    {s : Set (Position I)} (hs : ∀ᵐ x ∂volume, x ∉ s → u x = 0)
    (k : ℝ) (hb : ∀ x ∈ s, b x = k) : v = k • u := by
  apply Lp.ext
  filter_upwards [hrep, hs, Lp.coeFn_smul k u] with x hv hux hsmul
  have hpoint : b x • u x = k • u x := by
    by_cases hx : x ∈ s
    · exact congrArg (fun z : ℝ => z • u x) (hb x hx)
    · simp only [hux hx, smul_zero]
  exact hv.trans (hpoint.trans hsmul.symm)

theorem multiplier_eq_of_supported (a : DifferentiableMultiplier I) (u : L2 H I)
    {s : Set (Position I)} (hs : ∀ᵐ x ∂volume, x ∉ s → u x = 0)
    (k : ℝ) (ha : ∀ x ∈ s, a.weight x = k) : a.multiplier u = k • u :=
  scalar_map_eq u (a.multiplier u) a.weight
    (PhotonLocalization.realL2Multiplier_apply a.weight a.differentiable.continuous.aestronglyMeasurable
      a.bound (ae_of_all _ a.bounded) u) hs k ha

theorem derivativeMultiplier_eq_of_supported (a : DifferentiableMultiplier I) (i : I) (u : L2 H I)
    {s : Set (Position I)} (hs : ∀ᵐ x ∂volume, x ∉ s → u x = 0)
    (k : ℝ) (ha : ∀ x ∈ s, a.gradient i x = k) : a.derivativeMultiplier i u = k • u :=
  scalar_map_eq u (a.derivativeMultiplier i u) (a.gradient i)
    (PhotonLocalization.realL2Multiplier_apply (a.gradient i) (a.gradient_measurable i).aestronglyMeasurable
      a.derivativeBound (ae_of_all _ (a.derivative_bounded i)) u) hs k ha

theorem cutoff_action {O : Position I} (family : BufferedFamily O)
    {r : ℝ} (hr : 0 < r) (u : L2 H I)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball O r → u x = 0) :
    (family.cutoff r).scalar.multiplier u = u ∧
      (∀ i, ((family.cutoff r).derivative i).multiplier u = 0) ∧
      ∀ i, ((family.cutoff r).derivative i).derivativeMultiplier i u = 0 := by
  have hweight : ∀ x ∈ Metric.ball O r, (family.cutoff r).scalar.weight x = 1 := by
    intro x hx
    exact (congrArg (fun w : Position I → ℝ => w x) (family.weight r hr)).trans
      (buffered_scaled_one hr (by
        change dist x O ≤ 5 * r / 4
        have hdist := Metric.mem_ball.mp hx
        linarith only [hdist, hr]))
  have hderiv (x : Position I) (hx : x ∈ Metric.ball O r) :=
    buffered_derivatives_supported (family.cutoff r) hr (family.weight r hr) x
      (fun h => h.2 hx)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_smul] using multiplier_eq_of_supported (family.cutoff r).scalar u hs 1 hweight
  · intro i
    apply (multiplier_eq_of_supported ((family.cutoff r).derivative i) u hs 0 ?_).trans (zero_smul _ _)
    intro x hx
    exact (congrArg (fun w : Position I → ℝ => w x) ((family.cutoff r).derivative_weight i)).trans
      ((hderiv x hx).1 i)
  · intro i
    exact (derivativeMultiplier_eq_of_supported ((family.cutoff r).derivative i) i u hs 0
      (fun x hx => (hderiv x hx).2 i i)).trans (zero_smul _ _)

theorem cutoff_supported {O : Position I} (family : BufferedFamily O)
    {r : ℝ} (hr : 0 < r) (x : Position I) (hx : x ∉ Metric.ball O (2 * r)) :
    (family.cutoff r).scalar.weight x = 0 :=
  (congrArg (fun w : Position I → ℝ => w x) (family.weight r hr)).trans
    (buffered_scaled_zero hr (by have hh : 2 * r ≤ dist x O := not_lt.mp hx; linarith only [hh, hr]))

theorem weighted_integral_on_eq (a : DifferentiableMultiplier I) (u : L2 H I)
    (w : Position I → ℝ) {s : Set (Position I)} (hs : MeasurableSet s)
    (ha : ∀ x ∈ s, a.weight x = 1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ s → a.multiplier u x = 0)
    (hi : Integrable (fun x => w x * ‖a.multiplier u x‖ ^ 2)) :
    IntegrableOn (fun x => w x * ‖u x‖ ^ 2) s ∧
      (∫ x, w x * ‖a.multiplier u x‖ ^ 2) = ∫ x in s, w x * ‖u x‖ ^ 2 := by
  have hrep : (a.multiplier u : Position I → H) =ᵐ[volume] fun x => a.weight x • u x :=
    PhotonLocalization.realL2Multiplier_apply a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded) u
  have heq : (fun x => w x * ‖a.multiplier u x‖ ^ 2) =ᵐ[volume.restrict s]
      fun x => w x * ‖u x‖ ^ 2 := by
    filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae hrep] with x hx hrepX
    have hv : a.multiplier u x = u x :=
      hrepX.trans ((congrArg (fun z : ℝ => z • u x) (ha x hx)).trans (one_smul _ _))
    exact congrArg (fun z : H => w x * ‖z‖ ^ 2) hv
  have hz : ∀ᵐ x ∂volume, x ∉ s → w x * ‖a.multiplier u x‖ ^ 2 = 0 := by
    filter_upwards [hsupp] with x hx hnot
    simp only [hx hnot, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  exact ⟨hi.integrableOn.congr heq,
    (setIntegral_eq_integral_of_ae_compl_eq_zero hz).symm.trans (integral_congr_ae heq)⟩

end PfHk.BufferedCutoffLocality
