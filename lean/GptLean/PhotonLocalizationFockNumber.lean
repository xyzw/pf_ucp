import GptLean.PhotonLocalizationFockChannel
import GptLean.PhotonLocalizationChannelMeasurement
import GptLean.PhotonLocalizationChannelGentle
import GptLean.PhotonCompactness

/-!
The joint retained/discarded photon law of the constructed Fock channel.

The background is uniform Fock sector calculus on vectors. Joint sector
masses are actual squared coordinates and bounded number functions are
identified with their spectral sums. Normality and nonnegative Fubini
supply the mixed-state law. The gentle estimate is derived from the
positive vacuum second-quantization operator and the rank-one trace norm.
The downstream constructor uses this law to supply the retained-limit
interface for the explicit smooth-cutoff channel.
-/

namespace GptLean.PhotonLocalizationFockChannel

open MeasureTheory
open PhotonLocalizationChannel PhotonLocalizationKernelCutoffs

/-- Bounded nonnegative functions of photon number. -/
def NumberWeight := {w : ℕ → ℝ // ∀ n, 0 ≤ w n ∧ w n ≤ 1}

def tailWeight (M : ℕ) : NumberWeight :=
  ⟨fun n => if M < n then 1 else 0, fun n => by dsimp; split_ifs <;> norm_num⟩

noncomputable def geometricWeight : NumberWeight :=
  ⟨fun n => (1 / 2 : ℝ) ^ n, fun n =>
    ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩⟩

variable {h H T G : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- Universal direct-sum Fock sector identities, before normal-state
extension. `joint` resolves each vector into retained/discarded number
sectors. The two spectral identities are the retained marginal and
additivity of total number under the exponential law. The vacuum
positivity field is the usual order property of second quantization of
a positive one-photon contraction. None of the fields mention a radius. -/
structure NumberCalculus (R : Gaussian.RankOneData H T) (F : FockFactorization h H)
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G] where
  joint : (h →ₗᵢ[ℂ] WithLp 2 (h × h)) → H →ₗᵢ[ℂ] lp (fun _ : ℕ × ℕ => G) 2
  quadratic : QuadraticTrace (G := G) R
  vacuumTrace : QuadraticTrace (G := H) R
  numberTest : NumberWeight → T →L[ℝ] ℝ
  retained_spectral : ∀ (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (w : NumberWeight) (v : H),
    (∑' p : ℕ × ℕ, w.val p.1 * ‖joint j v p‖ ^ 2) =
      ∑' a, numberTest w (R.rankOne (F.factor j v a))
  total_spectral : ∀ (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (w : NumberWeight) (v : H),
    (∑' p : ℕ × ℕ, w.val (p.1 + p.2) * ‖joint j v p‖ ^ 2) =
      numberTest w (R.rankOne v)
  vacuum_spectral : ∀ (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (v : H),
    (∑' p : ℕ × ℕ, if 1 ≤ p.2 then ‖joint j v p‖ ^ 2 else 0) =
      ‖v‖ ^ 2 - ‖F.factor j v 0‖ ^ 2
  vacuum_positive : ∀ (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)),
    (∀ u v, inner ℂ (retainedMap j u) v = inner ℂ u (retainedMap j v)) →
    (∀ u, ‖retainedMap j u‖ ^ 2 ≤ (inner ℂ u (retainedMap j u)).re) →
    ∀ v, ‖F.factor j v 0‖ ^ 2 ≤ (inner ℂ v (F.factor j v 0)).re

namespace NumberCalculus

variable {R : Gaussian.RankOneData H T} {F : FockFactorization h H}
  (C : NumberCalculus R F G)

/-- The actual bounded joint-sector effect. -/
noncomputable def jointEffect (j : h →ₗᵢ[ℂ] WithLp 2 (h × h))
    (p : ℕ × ℕ) : T →L[ℝ] ℝ :=
  C.quadratic.sectorEffect (C.joint j) p

@[simp] theorem jointEffect_rankOne (j : h →ₗᵢ[ℂ] WithLp 2 (h × h))
    (p : ℕ × ℕ) (v : H) : C.jointEffect j p (R.rankOne v) = ‖C.joint j v p‖ ^ 2 :=
  C.quadratic.sectorEffect_rankOne _ _ _

/-- The bounded effect of a nonvacuum environment. -/
noncomputable def lossEffect (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) : T →L[ℝ] ℝ :=
  R.trace - C.vacuumTrace.effect
    ((lp.evalCLM ℂ (fun _ : ℕ => H) 2 0).comp (F.factor j).toContinuousLinearMap)

omit [CompleteSpace T] in
@[simp] theorem lossEffect_rankOne (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (v : H) :
    C.lossEffect j (R.rankOne v) = ‖v‖ ^ 2 - ‖F.factor j v 0‖ ^ 2 := by
  change R.trace (R.rankOne v) -
    C.vacuumTrace.effect
      ((lp.evalCLM ℂ (fun _ : ℕ => H) 2 0).comp (F.factor j).toContinuousLinearMap)
      (R.rankOne v) = _
  rw [R.trace_rankOne, C.vacuumTrace.rankOne]
  rfl

noncomputable def tail (M : ℕ) : T →L[ℝ] ℝ := C.numberTest (tailWeight M)

noncomputable def weight : T →L[ℝ] ℝ := C.numberTest geometricWeight

private theorem sector_mass (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (v : H) :
    Summable (fun p : ℕ × ℕ => ‖C.joint j v p‖ ^ 2) := by
  simpa only [C.quadratic.sectorEffect_rankOne] using
    (C.quadratic.sectorEffect_pure_hasSum (C.joint j) v).summable

private theorem weighted_summable (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (v : H)
    (w : ℕ × ℕ → ℝ) (hw : ∀ p, 0 ≤ w p ∧ w p ≤ 1) :
    Summable (fun p : ℕ × ℕ => w p * ‖C.joint j v p‖ ^ 2) :=
  PhotonLoss.summable_weight_mul (fun _ => sq_nonneg _) (C.sector_mass j v)
    (fun p => (hw p).1) (fun p => (hw p).2)

/-- The retained number functional is obtained by summing the actual
Kraus output, then justified on all positive normal states. -/
theorem retained_hasSum (N : NormalTraceData R)
    (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (w : NumberWeight)
    {x : T} (hx : x ∈ R.positive) :
    HasSum (fun p : ℕ × ℕ => w.val p.1 * C.jointEffect j p x)
      (C.numberTest w (N.extend (F.factor j) x)) := by
  apply N.measurement_weighted (C.jointEffect j)
    ((C.numberTest w).comp (N.extend (F.factor j))) (fun p => w.val p.1)
    (fun p => (w.property p.1).1)
    (fun p v => by rw [C.jointEffect_rankOne]; positivity) _ hx
  intro v
  simp only [ContinuousLinearMap.comp_apply, N.extend_rankOne, C.jointEffect_rankOne]
  convert (C.weighted_summable j v (fun p => w.val p.1)
    (fun p => w.property p.1)).hasSum using 1
  exact ((C.retained_spectral j w v).trans
    ((C.numberTest w).hasSum (pure_hasSum R (F.factor j) v)).tsum_eq).symm

/-- Number conservation under Fock factorization yields the total-number
functional of the original state from the joint sector law. -/
theorem total_hasSum (N : NormalTraceData R)
    (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (w : NumberWeight)
    {x : T} (hx : x ∈ R.positive) :
    HasSum (fun p : ℕ × ℕ => w.val (p.1 + p.2) * C.jointEffect j p x)
      (C.numberTest w x) := by
  apply N.measurement_weighted (C.jointEffect j) (C.numberTest w)
    (fun p => w.val (p.1 + p.2)) (fun p => (w.property (p.1 + p.2)).1)
    (fun p v => by rw [C.jointEffect_rankOne]; positivity) _ hx
  intro v
  simp only [C.jointEffect_rankOne]
  exact (C.total_spectral j w v) ▸
    (C.weighted_summable j v (fun p => w.val (p.1 + p.2))
      (fun p => w.property (p.1 + p.2))).hasSum

/-- The nonvacuum part of the joint law equals the standard loss effect. -/
theorem discard_eq (N : NormalTraceData R)
    (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) {x : T} (hx : x ∈ R.positive) :
    PhotonLoss.discardProb (fun p => C.jointEffect j p x) = C.lossEffect j x := by
  have hh : HasSum (fun p : ℕ × ℕ => (if 1 ≤ p.2 then (1 : ℝ) else 0) * C.jointEffect j p x)
      (C.lossEffect j x) := by
    apply N.measurement_weighted (C.jointEffect j) (C.lossEffect j)
      (fun p => if 1 ≤ p.2 then 1 else 0)
      (fun p => by split_ifs <;> norm_num)
      (fun p v => by rw [C.jointEffect_rankOne]; positivity) _ hx
    intro v
    have hs := PhotonLoss.summable_ite (fun p : ℕ × ℕ => sq_nonneg ‖C.joint j v p‖)
      (C.sector_mass j v) (fun p => 1 ≤ p.2)
    simpa only [C.jointEffect_rankOne, ite_mul, one_mul, zero_mul, C.lossEffect_rankOne,
      C.vacuum_spectral j v] using hs.hasSum
  simpa only [PhotonLoss.discardProb, ite_mul, one_mul, zero_mul] using hh.tsum_eq

/-- The physical mixed-state joint law, including its derived gentle
bound. Only the universal vector Fock identities enter as background. -/
noncomputable def numberLaw (N : NormalTraceData R) (M : RankOneMetric R)
    (j : h →ₗᵢ[ℂ] WithLp 2 (h × h))
    (hself : ∀ u v, inner ℂ (retainedMap j u) v = inner ℂ u (retainedMap j v))
    (hpos : ∀ u, ‖retainedMap j u‖ ^ 2 ≤ (inner ℂ u (retainedMap j u)).re)
    {x : T} (hx : x ∈ N.states) :
    PhotonLoss.LocalizationNumberLaw (fun M x => C.tail M x) (fun x => C.weight x)
      x (N.extend (F.factor j) x) where
  p p := C.jointEffect j p x
  nonneg p := C.quadratic.sectorEffect_nonneg N (C.joint j) p hx.1
  summable := (C.quadratic.sectorEffect_hasSum N (C.joint j) hx.1).summable
  normalized := (C.quadratic.sectorEffect_hasSum N (C.joint j) hx.1).tsum_eq.trans hx.2
  tail_eq M := by
    simpa only [tail, tailWeight, PhotonLoss.tailIn, ite_mul, one_mul, zero_mul] using
      (C.retained_hasSum N j (tailWeight M) hx.1).tsum_eq.symm
  weight_in := by
    simpa only [weight, geometricWeight, PhotonLoss.bIn] using
      (C.retained_hasSum N j geometricWeight hx.1).tsum_eq.symm
  weight_total := by
    simpa only [weight, geometricWeight, PhotonLoss.bTot] using
      (C.total_hasSum N j geometricWeight hx.1).tsum_eq.symm
  gentle := by
    rw [C.discard_eq N j hx.1]
    apply N.gentle_state M (F.factor j) (C.lossEffect j) (C.lossEffect_rankOne j) _ hx
    intro v
    rw [norm_sub_sq (𝕜 := ℂ)]
    have hp := C.vacuum_positive j hself hpos v
    change ‖v‖ ^ 2 - 2 * (inner ℂ v (F.factor j v 0)).re + ‖F.factor j v 0‖ ^ 2 ≤ _
    linarith

end NumberCalculus


end GptLean.PhotonLocalizationFockChannel
