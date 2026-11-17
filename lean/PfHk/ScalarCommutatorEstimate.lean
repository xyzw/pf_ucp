import PfHk.PhysicalCutoffCommutatorAlgebraLp

noncomputable section
namespace PfHk.PhysicalCutoffCommutator

open MeasureTheory Filter GptLean GptLean.ElectronicH1Multiplier GptLean.ElectronicH1Space
open scoped InnerProductSpace Topology ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

variable {I : Type} [Fintype I] [DecidableEq I]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def laplacian (a : TwiceDifferentiableMultiplier I) (x : EuclideanSpace ℝ I) : ℝ :=
  ∑ i, (a.derivative i).gradient i x

omit [CompleteSpace H] in
private theorem multiplier_ae (a : DifferentiableMultiplier I) (u : L2 H I) :
    a.multiplier (H := H) u =ᵐ[volume] fun x => (a.weight x : ℂ) • u x := by
  unfold DifferentiableMultiplier.multiplier
  simpa only [Complex.coe_smul] using PhotonLocalization.realL2Multiplier_apply a.weight
    a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded) u

omit [CompleteSpace H] in
private theorem derivativeMultiplier_ae (a : DifferentiableMultiplier I) (i : I) (u : L2 H I) :
    a.derivativeMultiplier (H := H) i u =ᵐ[volume] fun x => (a.gradient i x : ℂ) • u x := by
  unfold DifferentiableMultiplier.derivativeMultiplier
  simpa only [Complex.coe_smul] using PhotonLocalization.realL2Multiplier_apply (a.gradient i)
    (a.gradient_measurable i).aestronglyMeasurable a.derivativeBound
    (ae_of_all _ (a.derivative_bounded i)) u

theorem scalar_commutator_ae (a : TwiceDifferentiableMultiplier I) (ψ : L2 H I) (D : I → L2 H I) :
    scalarCommutator a ψ D =ᵐ[volume] fun x =>
      (-Complex.I) • (∑ i, (a.scalar.gradient i x : ℂ) •
        D i x) +
        (-(laplacian a x / 2) : ℂ) • ψ x := by
  let T : I → L2 H I := fun i =>
    (-Complex.I) • (a.derivative i).multiplier (H := H) (D i) +
      (-(1 / 2) : ℂ) • (a.derivative i).derivativeMultiplier (H := H) i ψ
  have hT : ∀ i, ∀ᵐ x ∂volume, T i x =
      (-Complex.I) • ((a.scalar.gradient i x : ℂ) • D i x) +
        (-(1 / 2) : ℂ) • (((a.derivative i).gradient i x : ℂ) • ψ x) := by
    intro i
    filter_upwards [Lp.coeFn_add ((-Complex.I) • (a.derivative i).multiplier (H := H) (D i))
        ((-(1 / 2) : ℂ) • (a.derivative i).derivativeMultiplier (H := H) i ψ),
      Lp.coeFn_smul (-Complex.I) ((a.derivative i).multiplier (H := H) (D i)),
      Lp.coeFn_smul (-(1 / 2) : ℂ) ((a.derivative i).derivativeMultiplier (H := H) i ψ),
      multiplier_ae (a.derivative i) (D i), derivativeMultiplier_ae (a.derivative i) i ψ]
      with x h₁ h₂ h₃ h₄ h₅
    simp only [T, h₁, Pi.add_apply, h₂, h₃, Pi.smul_apply, h₄, h₅, a.derivative_weight]
  have hall : ∀ᵐ x ∂volume, ∀ i, T i x =
      (-Complex.I) • ((a.scalar.gradient i x : ℂ) • D i x) +
        (-(1 / 2) : ℂ) • (((a.derivative i).gradient i x : ℂ) • ψ x) :=
    (ae_all_iff).mpr hT
  filter_upwards [Lp.coeFn_finsetSum Finset.univ T, hall] with x hx hallx
  change (∑ i, T i) x = _
  rw [hx]
  simp only [Finset.sum_apply, hallx, Finset.sum_add_distrib]
  rw [← Finset.smul_sum, ← Finset.smul_sum, ← Finset.sum_smul]
  simp only [← Complex.ofReal_sum, smul_smul]
  congr 1
  congr 1
  simp only [laplacian]
  ring

theorem scalar_commutator_norm_sq_ae (a : TwiceDifferentiableMultiplier I) (ψ : L2 H I) (D : I → L2 H I) :
    ∀ᵐ x ∂volume,
      ‖scalarCommutator a ψ D x‖ ^ 2 ≤
        2 * (∑ i, a.scalar.gradient i x ^ 2) *
          (∑ i, ‖D i x‖ ^ 2) +
        (1 / 2 : ℝ) * laplacian a x ^ 2 * ‖ψ x‖ ^ 2 := by
  filter_upwards [scalar_commutator_ae a ψ D] with x hx
  rw [hx]
  exact cutoff_commutator_norm_sq (fun i => a.scalar.gradient i x) (laplacian a x)
    (fun i => D i x)
    (ψ x)

/-- Weighted integral bound with the actual physical covariant derivative
and actual local L2 masses. It also proves integrability of the left side. -/
theorem scalar_weighted_commutator_bound (a : TwiceDifferentiableMultiplier I) (ψ : L2 H I) (D : I → L2 H I)
    {s : Set (EuclideanSpace ℝ I)} (hs : MeasurableSet s) {w : EuclideanSpace ℝ I → ℝ}
    (hwm : AEStronglyMeasurable w volume) (hw0 : ∀ x, 0 ≤ w x)
    {W G L : ℝ} (_hW : 0 ≤ W) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hw : ∀ x ∈ s, w x ≤ W)
    (hgrad : ∀ x ∈ s, ∑ i, a.scalar.gradient i x ^ 2 ≤ G)
    (hlap : ∀ x ∈ s, laplacian a x ^ 2 ≤ L)
    (houtgrad : ∀ x ∉ s, ∀ i, a.scalar.gradient i x = 0)
    (houtlap : ∀ x ∉ s, laplacian a x = 0) :
    Integrable (fun x => w x * ‖scalarCommutator a ψ D x‖ ^ 2)
      volume ∧
    (∫ x, w x * ‖scalarCommutator a ψ D x‖ ^ 2) ≤
      W * (2 * G * (∑ i, (∫ x in s, ‖D i x‖ ^ 2)) +
          (1 / 2 : ℝ) * L * (∫ x in s, ‖ψ x‖ ^ 2)) := by
  let f := fun x => w x * ‖scalarCommutator a ψ D x‖ ^ 2
  let b := fun x => W * (2 * G * (∑ i, ‖D i x‖ ^ 2) + (1 / 2 : ℝ) * L * ‖ψ x‖ ^ 2)
  have hb : Integrable b volume := by
    apply Integrable.const_mul
    apply Integrable.add
    · exact (integrable_finsetSum _ fun i _ => (Lp.memLp (D i)).norm.integrable_sq).const_mul _
    · exact (Lp.memLp ψ).norm.integrable_sq.const_mul _
  have hbi : Integrable (s.indicator b) volume := hb.indicator hs
  have hf0 : ∀ x, 0 ≤ f x := fun x => mul_nonneg (hw0 x) (sq_nonneg _)
  have hle : f ≤ᵐ[volume] s.indicator b := by
    filter_upwards [scalar_commutator_norm_sq_ae a ψ D]
      with x hx
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs]
      have hD : 0 ≤ ∑ i, ‖D i x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hpoint : ‖scalarCommutator a ψ D x‖ ^ 2 ≤
          2 * G * (∑ i, ‖D i x‖ ^ 2) + (1 / 2 : ℝ) * L * ‖ψ x‖ ^ 2 := by
        apply hx.trans
        exact add_le_add (mul_le_mul_of_nonneg_right (by linarith [hgrad x hxs]) hD)
          (mul_le_mul_of_nonneg_right (by linarith [hlap x hxs]) (sq_nonneg _))
      exact (mul_le_mul_of_nonneg_left hpoint (hw0 x)).trans
        (mul_le_mul_of_nonneg_right (hw x hxs) (by positivity))
    · rw [Set.indicator_of_notMem hxs]
      have hz : ‖scalarCommutator a ψ D x‖ ^ 2 = 0 := by
        apply le_antisymm _ (sq_nonneg _)
        simpa only [houtgrad x hxs, houtlap x hxs, zero_pow (by norm_num : 2 ≠ 0),
          Finset.sum_const_zero, mul_zero, zero_mul, add_zero] using hx
      simp only [f, hz, mul_zero, le_refl]
  have hfi : Integrable f volume := hbi.mono'
    (hwm.mul ((Lp.aestronglyMeasurable _).norm.pow 2)) (by
      filter_upwards [hle] with x hx
      simpa only [Real.norm_of_nonneg (hf0 x)] using hx)
  refine ⟨hfi, ?_⟩
  calc
    ∫ x, f x ≤ ∫ x, s.indicator b x := integral_mono_ae hfi hbi hle
    _ = _ := by
      rw [integral_indicator hs]
      simp only [b, integral_const_mul, integral_add
        ((integrable_finsetSum _ fun i _ => (Lp.memLp (D i)).norm.integrable_sq).const_mul _).integrableOn
        ((Lp.memLp ψ).norm.integrable_sq.const_mul _).integrableOn,
        integral_finsetSum _ (fun i _ => (Lp.memLp (D i)).norm.integrable_sq.integrableOn)]


end PfHk.PhysicalCutoffCommutator
