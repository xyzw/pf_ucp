import GptLean.RemovalConstraints
import GptLean.Repair.WeightedFormDomain

/-!
Canonical current evaluation is stated once on every PF reference-domain
vector. The actual coordinate repair current then follows from the weak
product theorem and the unbounded field graph, on the very same channel
vectors and source covariant derivative used by the energy calculation.
-/

noncomputable section

namespace GptLean.RemovalPhysicalCurrent

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open MeasureTheory Filter Repair SymmetricLift RemovalState
open scoped Topology ENNReal

variable {I V H T Test : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {Tr : PositiveTraceData T} {E : PositiveForm Tr}

/-- The standard rank-one current formula on the entire reference
domain. It mentions no repair, localization, channel, or output vector. -/
def CanonicalCurrent
    (rankOne : Gaussian.RankOneData (Lp H 2 (volume : Measure (EuclideanSpace ℝ I))) T)
    (radiation : H →ₗ.[ℂ] H)
    (field : I → EuclideanSpace ℝ I → H →ₗ.[ℂ] H) (e : ℝ)
    (current : Test → FormObservable E) (weight : Test → EuclideanSpace ℝ I → ℝ)
    (direction : Test → I) : Prop :=
  ∀ (t : Test) (ψ : EuclideanSpace ℝ I → H)
    (dψ aψ : I → EuclideanSpace ℝ I → H) (hψ : MemLp ψ 2 volume),
    InPFReferenceDomain radiation ψ → HasWeakH1Local ψ dψ →
    (∀ j, MemLp (dψ j) 2 volume) → (∀ j, MemLp (aψ j) 2 volume) →
    (∀ j, ∀ᵐ x ∂volume, (ψ x, aψ j x) ∈ (field j x).graph) →
    Tendsto (fun n => (current t).approximation n (rankOne.rankOne (hψ.toLp ψ))) atTop
      (𝓝 ((∫ x, inner ℂ (ψ x)
        ((weight t x : ℂ) • (-Complex.I • dψ (direction t) x -
          (e : ℂ) • aψ (direction t) x)) ∂volume).re))

/-- The tested channel derivative is a scalar multiple of the identical
directional channel derivative used in the kinetic energy. -/
theorem weighted_channelDerivative (b : HilbertBasis ℕ ℂ V)
    (z dz : EuclideanSpace ℝ I → V) (u ψ : EuclideanSpace ℝ I → H)
    (w : EuclideanSpace ℝ I → ℝ) (a : ℕ) (x : EuclideanSpace ℝ I) :
    channelDerivative b z (fun y => (w y : ℂ) • dz y)
      (fun y => (w y : ℂ) • u y) ψ a x =
      (w x : ℂ) • channelDerivative b z dz u ψ a x := by
  simp only [channelDerivative, coordinate, inner_smul_right, smul_sub, smul_smul]
  module

/-- A universal canonical formula gives the current limit for the actual
coordinate channel. Its covariant product rule is proved from weak H1
and unbounded-field graph membership, rather than assumed at the output. -/
theorem canonical_current_coordinate
    (rankOne : Gaussian.RankOneData (Lp H 2 (volume : Measure (EuclideanSpace ℝ I))) T)
    (radiation : H →ₗ.[ℂ] H)
    (field : I → EuclideanSpace ℝ I → H →ₗ.[ℂ] H) (e : ℝ)
    (current : Test → FormObservable E) (weight : Test → EuclideanSpace ℝ I → ℝ)
    (direction : Test → I)
    (hcanonical : CanonicalCurrent rankOne radiation field e current weight direction)
    (b : HilbertBasis ℕ ℂ V)
    {z : EuclideanSpace ℝ I → V} {dz : I → EuclideanSpace ℝ I → V}
    {ψ rψ : EuclideanSpace ℝ I → H} {dψ aψ u : I → EuclideanSpace ℝ I → H}
    (hz : HasWeakH1Local z dz) (hunit : ∀ᵐ x ∂volume, ‖z x‖ ≤ 1)
    (hψ : MemLp ψ 2 volume) (hweak : HasWeakH1Local ψ dψ)
    (hdψ : ∀ j, MemLp (dψ j) 2 volume) (hrψ : MemLp rψ 2 volume)
    (hrad : ∀ᵐ x ∂volume, (ψ x, rψ x) ∈ radiation.graph)
    (hweight : ∀ j, Integrable (fun x => ‖dz j x‖ ^ 2 * ‖ψ x‖ ^ 2) volume)
    (haψ : ∀ j, MemLp (aψ j) 2 volume)
    (hfield : ∀ j, ∀ᵐ x ∂volume, (ψ x, aψ j x) ∈ (field j x).graph)
    (hu : ∀ j, ∀ᵐ x ∂volume, u j x = -Complex.I • dψ j x - (e : ℂ) • aψ j x)
    (a : ℕ) (v : Lp H 2 (volume : Measure (EuclideanSpace ℝ I)))
    (hv : (fun x => v x) =ᵐ[volume] channelValue b z ψ a) (t : Test) :
    Tendsto (fun n => (current t).approximation n (rankOne.rankOne v)) atTop
      (𝓝 ((∫ x, inner ℂ (channelValue b z ψ a x)
        (channelDerivative b z (fun y => (weight t y : ℂ) • dz (direction t) y)
          (fun y => (weight t y : ℂ) • u (direction t) y) ψ a x) ∂volume).re)) := by
  let k := fun x => coordinate b (z x) a
  let dk := fun j x => coordinate b (dz j x) a
  have hk : HasWeakH1Local k dk :=
    weakH1Local_map ((innerSL ℂ (b a)).restrictScalars ℝ) hz
  have hb : ∀ᵐ x ∂volume, ‖k x‖ ≤ 1 :=
    hunit.mono (fun x hx => (coordinate_norm_le b (z x) a).trans hx)
  have hw (j : I) : MemLp (fun x => dk j x • ψ x) 2 volume :=
    coordinate_weighted_derivative_memLp b hz hψ hweight a j
  obtain ⟨hout, hprod, hdprod, hrprod, hradprod⟩ :=
    pf_reference_product_of_weighted radiation hk hb hψ hweak hdψ hrψ hrad hw
  have hkTop : MemLp k ∞ volume := memLp_top_of_bound
    (finite_localMemLp_two_locallyIntegrable hk.function_memLp).aestronglyMeasurable 1 hb
  have ha (j : I) : MemLp (fun x => k x • aψ j x) 2 volume := (haψ j).smul hkTop
  have hg (j : I) : ∀ᵐ x ∂volume,
      (k x • ψ x, k x • aψ j x) ∈ (field j x).graph := by
    filter_upwards [hfield j] with x hx
    exact (field j x).graph.smul_mem (k x) hx
  have href : InPFReferenceDomain radiation (fun x => k x • ψ x) :=
    ⟨hout, _, _, hprod, hdprod, hrprod, hradprod⟩
  have hv' : hout.toLp (fun x => k x • ψ x) = v := by
    apply Lp.ext
    exact hout.coeFn_toLp.trans hv.symm
  have hc := hcanonical t (fun x => k x • ψ x)
    (fun j x => k x • dψ j x + dk j x • ψ x)
    (fun j x => k x • aψ j x) hout href hprod hdprod ha hg
  rw [hv'] at hc
  have he : (∫ x, inner ℂ (k x • ψ x)
      ((weight t x : ℂ) • (-Complex.I • (k x • dψ (direction t) x + dk (direction t) x • ψ x) -
        (e : ℂ) • (k x • aψ (direction t) x))) ∂volume) =
      ∫ x, inner ℂ (channelValue b z ψ a x)
        (channelDerivative b z (fun y => (weight t y : ℂ) • dz (direction t) y)
          (fun y => (weight t y : ℂ) • u (direction t) y) ψ a x) ∂volume := by
    apply integral_congr_ae
    filter_upwards [hu (direction t)] with x hx
    rw [weighted_channelDerivative]
    simp only [channelDerivative]
    rw [hx]
    congr 2
    simp only [channelDerivative, k, dk, smul_add, smul_sub, neg_smul, smul_smul]
    module
  simpa only [he] using hc

end GptLean.RemovalPhysicalCurrent
