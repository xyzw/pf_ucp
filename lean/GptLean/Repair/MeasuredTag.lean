import GptLean.Repair.Multipliers
import GptLean.Repair.LiftSections
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
The concrete six-component repair tag with a measurable wavenumber choice.
The zero-velocity branch is spatially constant. Thus it has zero repair
cost and introduces no discontinuous choice of basis or lift. For a
nonzero velocity bound the wavenumber is the explicit one in the paper.
Joint measurability follows from the original velocity and scalar bounds,
rather than being supplied for the resulting one-particle tag.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Repair

open MeasureTheory TopologicalSpace GptLean.Multipliers

abbrev SixTag := EuclideanSpace ℂ (Fin 3 × Bool)

def selectedWaveNumber (V M : ℝ) : ℝ :=
  if V = 0 then 0 else Real.sqrt (max (36 * V ^ 2) M)

def selectedTag (V M : ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) : SixTag :=
  WithLp.toLp 2 (fun k => K (selectedWaveNumber V M) v k x)

theorem selectedTag_zero (M : ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) :
    selectedTag 0 M v x = WithLp.toLp 2 (fun _ : Fin 3 × Bool => ((1 / Real.sqrt 6 : ℝ) : ℂ)) := by
  ext k
  simp [selectedTag, selectedWaveNumber, K, amp, apVal]

/-- The zero branch is independent of position, including before any
regularity or representative choices for the measured field. -/
theorem selectedTag_zero_constant (M : ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (x y : Fin 3 → ℝ) : selectedTag 0 M v x = selectedTag 0 M v y := by
  rw [selectedTag_zero, selectedTag_zero]

theorem selectedTag_norm (V M : ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (hV : 0 ≤ V) (x : Fin 3 → ℝ) (hv : ∀ i, |v x i| ≤ V) :
    ‖selectedTag V M v x‖ = 1 := by
  have hs : ‖selectedTag V M v x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    by_cases hzero : V = 0
    · subst V
      simp only [selectedTag_zero, PiLp.toLp_apply, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, div_pow, one_pow]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
      norm_num
    · have hpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hzero)
      have h3 := three_mul_lt_sqrt_max hpos M
      change (∑ k, ‖K (selectedWaveNumber V M) v k x‖ ^ 2) = 1
      simp only [selectedWaveNumber, hzero, ite_false]
      apply sum_norm_sq_K (by linarith)
      intro i
      linarith [hv i]
  nlinarith [norm_nonneg (selectedTag V M v x)]

/-- The derivative coordinates are actual one-dimensional derivatives,
including the constant zero-velocity branch. -/
def selectedTagDerivative (V M : ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) (ν : Fin 3) : SixTag :=
  WithLp.toLp 2 (fun k => pderiv (fun y => selectedTag V M v y k) x ν)

theorem selectedTagDerivative_zero (M : ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) (ν : Fin 3) : selectedTagDerivative 0 M v x ν = 0 := by
  ext k
  simp [selectedTagDerivative, selectedTag_zero, pderiv]

/-- Every selected tag coordinate is differentiable along coordinate
lines when the original velocity is. The derivative is the one used in
the connection and metric statements below. -/
theorem selectedTag_coordinate_hasDerivAt {V M : ℝ}
    {v : (Fin 3 → ℝ) → Fin 3 → ℝ} {dv : Fin 3 → Fin 3 → ℝ}
    {x : Fin 3 → ℝ} (hV : 0 ≤ V) (hvV : ∀ μ, |v x μ| ≤ V)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (x + s •
      (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ) (dv μ ν) 0)
    (k : Fin 3 × Bool) (ν : Fin 3) :
    HasDerivAt (fun s : ℝ => selectedTag V M v
      (x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) k)
      (selectedTagDerivative V M v x ν k) 0 := by
  by_cases hzero : V = 0
  · subst V
    simpa only [selectedTag_zero, PiLp.toLp_apply, selectedTagDerivative_zero,
      PiLp.zero_apply] using hasDerivAt_const (0 : ℝ) ((1 / Real.sqrt 6 : ℝ) : ℂ)
  · have hpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hzero)
    have h3 := three_mul_lt_sqrt_max hpos M
    have hq : 0 < Real.sqrt (max (36 * V ^ 2) M) := by linarith
    have hadmissible : ∀ μ, 3 * |v x μ| < Real.sqrt (max (36 * V ^ 2) M) :=
      fun μ => by linarith [hvV μ]
    simpa only [selectedTagDerivative, selectedTag, selectedWaveNumber, hzero,
      ite_false, PiLp.toLp_apply, pderiv_K hq hadmissible hv] using
      hasDerivAt_K hq hadmissible hv k ν

/-- The explicit selected tag has the prescribed current connection in
both branches of the measurable choice. -/
theorem selectedTag_connection {V M : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {dv : Fin 3 → Fin 3 → ℝ} {x : Fin 3 → ℝ} (hV : 0 ≤ V)
    (hvV : ∀ μ, |v x μ| ≤ V)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (x + s •
      (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ) (dv μ ν) 0) (ν : Fin 3) :
    inner ℂ (selectedTag V M v x) (selectedTagDerivative V M v x ν) =
      Complex.I * (v x ν : ℂ) := by
  by_cases hzero : V = 0
  · subst V
    have hvzero : v x ν = 0 := abs_nonpos_iff.mp (hvV ν)
    simp [selectedTagDerivative_zero, hvzero]
  · have hpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hzero)
    have h3 := three_mul_lt_sqrt_max hpos M
    have hq : 0 < Real.sqrt (max (36 * V ^ 2) M) := by linarith
    have hadmissible : ∀ μ, 3 * |v x μ| < Real.sqrt (max (36 * V ^ 2) M) :=
      fun μ => by linarith [hvV μ]
    simpa only [selectedTag, selectedTagDerivative, selectedWaveNumber, hzero,
      ite_false, EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply,
      PiLp.toLp_apply, starRingEnd_apply, mul_comm] using sum_conj_K_mul_pderiv hq hadmissible hv ν

/-- The metric estimate is valid even when the selected wavenumber is
zero. It bounds the derivative of the actual six-component tag. -/
theorem selectedTag_metric_le {V M : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {dv : Fin 3 → Fin 3 → ℝ} {x : Fin 3 → ℝ} (hV : 0 ≤ V) (hM : 0 ≤ M)
    (hvV : ∀ μ, |v x μ| ≤ V) (hdv : ∑ μ, ∑ ν, (dv μ ν) ^ 2 ≤ M ^ 2)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (x + s •
      (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ) (dv μ ν) 0) :
    ∑ ν, ‖selectedTagDerivative V M v x ν‖ ^ 2 ≤ 36 * V ^ 2 + 2 * M := by
  by_cases hzero : V = 0
  · subst V
    simpa only [selectedTagDerivative_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, mul_zero, zero_add] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM
  · have hpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hzero)
    simp only [selectedTagDerivative, selectedTag, selectedWaveNumber, hzero,
      ite_false, EuclideanSpace.norm_sq_eq, PiLp.toLp_apply]
    rw [Finset.sum_comm]
    exact sum_norm_sq_pderiv_K_le hpos hM hvV hdv hv

section Measurability

variable {Q : Type*} [MeasurableSpace Q]

theorem selectedWaveNumber_measurable {V M : Q → ℝ}
    (hV : Measurable V) (hM : Measurable M) :
    Measurable (fun q => selectedWaveNumber (V q) (M q)) := by
  unfold selectedWaveNumber
  exact Measurable.ite (measurableSet_eq_fun hV measurable_const) measurable_const
    (((measurable_const.mul (hV.pow_const 2)).max hM).sqrt)

/-- Joint measurability of the scalar tag coordinates uses only elementary
measurable operations, including the chosen zero-velocity branch. -/
theorem selectedTag_coordinate_measurable {V M : Q → ℝ}
    {v x : Q → Fin 3 → ℝ} (hV : Measurable V) (hM : Measurable M)
    (hv : ∀ i, Measurable (fun q => v q i))
    (hx : ∀ i, Measurable (fun q => x q i)) (k : Fin 3 × Bool) :
    Measurable (fun q => K (selectedWaveNumber (V q) (M q)) (fun _ => v q) k (x q)) := by
  have hq := selectedWaveNumber_measurable hV hM
  unfold K apVal amp
  fun_prop

/-- This is the joint representative needed by the actual recursive-lift
channel. Its measurability is derived from the measured velocity. -/
theorem selectedTag_stronglyMeasurable {V M : Q → ℝ}
    {v x : Q → Fin 3 → ℝ} (hV : Measurable V) (hM : Measurable M)
    (hv : ∀ i, Measurable (fun q => v q i))
    (hx : ∀ i, Measurable (fun q => x q i)) :
    StronglyMeasurable (fun q => selectedTag (V q) (M q) (fun _ => v q) (x q)) := by
  apply Measurable.stronglyMeasurable
  exact (WithLp.measurable_toLp 2 _).comp
    (measurable_pi_lambda _ (selectedTag_coordinate_measurable hV hM hv hx))

/-- The concrete tag on Euclidean configuration space is jointly
measurable, as required by the recursive tensor lift. -/
theorem selectedTag_jointly_stronglyMeasurable
    {V M : Q → ℝ} {v : Q → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℝ}
    (hV : Measurable V) (hM : Measurable M)
    (hv : StronglyMeasurable (Function.uncurry v)) :
    StronglyMeasurable (fun p : Q × EuclideanSpace ℝ (Fin 3) =>
      selectedTag (V p.1) (M p.1) (fun y => v p.1 (WithLp.toLp 2 y))
        (WithLp.ofLp p.2)) := by
  have h := selectedTag_stronglyMeasurable (hV.comp measurable_fst)
    (hM.comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp hv.measurable)
    (fun i => (measurable_pi_apply i).comp
      ((WithLp.measurable_ofLp 2 _).comp measurable_snd))
  convert h using 1
  funext p
  rfl

/-- The selected one-particle tag gives measurable vectors for the actual
recursive repair channel, including all zero-velocity parameters. -/
theorem selectedTag_liftChannelSection_stronglyMeasurable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SeparableSpace H]
    (B : SymmetricLift.TensorBackground SixTag) (T : SymmetricLift.TensorMultilinearData B)
    (N : ℕ) (b : HilbertBasis ℕ ℂ (SymmetricLift.recursiveLiftCandidate B N).target)
    {V M : Q → ℝ} {v : Q → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℝ}
    {ψ : Q → SymmetricLift.Configuration N → H}
    (hV : Measurable V) (hM : Measurable M)
    (hv : StronglyMeasurable (Function.uncurry v))
    (hψ : StronglyMeasurable (Function.uncurry ψ)) (a : ℕ) :
    StronglyMeasurable (fun q => toL2Section (μ := volume)
      (fun r => channelValue b (SymmetricLift.recursiveLiftField B N
        (SymmetricLift.configurationTensor B
          (fun y => selectedTag (V r) (M r)
            (fun z => v r (WithLp.toLp 2 z)) (WithLp.ofLp y)))) (ψ r) a) q) := by
  exact recursiveLift_channelSection_stronglyMeasurable B T N b
    (selectedTag_jointly_stronglyMeasurable hV hM hv) hψ a

end Measurability
end GptLean.Repair
