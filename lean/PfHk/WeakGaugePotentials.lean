import PfHk.WeakGaugeAlgebra
import GptLean.TransformationsPotentials

/-! Weak gauge gradients define actual admissible vector potentials in
L-infinity plus L-three. The gauge action is defined on these classes. -/

noncomputable section

namespace GptLean.TransformationsGauge.WeakSpatialGauge

open MeasureTheory PhysicalPairSpace PhysicalPairDuality TransformationsPotentials
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 600000

private theorem exists_gradientPotential (G : WeakSpatialGauge) :
    ∃ A : VectorPotential, (A.val : Position → Vector) =ᵐ[volume] G.gradientVector := by
  choose a b ha hb he using G.gradient_in_sum
  let av : Position → Vector := fun x => WithLp.toLp 2 (fun i => a i x)
  let bv : Position → Vector := fun x => WithLp.toLp 2 (fun i => b i x)
  have hav : MemLp av 3 volume := MemLp.of_eval_piLp ha
  have hbv : MemLp bv ∞ volume := MemLp.of_eval_piLp hb
  refine ⟨ofParts (hbv.toLp bv) (hav.toLp av), ?_⟩
  have heAll : ∀ᵐ x ∂volume, ∀ i, G.gradient i x = a i x + b i x :=
    ae_all_iff.mpr he
  filter_upwards [coeFn_ofParts (hbv.toLp bv) (hav.toLp av), hbv.coeFn_toLp,
    hav.coeFn_toLp, heAll] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃]
  ext i
  change b i x + a i x = G.gradient i x
  rw [h₄ i, add_comm]

/-- The weak gradient as an admissible L-infinity plus L-three potential. -/
def gradientPotential (G : WeakSpatialGauge) : VectorPotential :=
  (exists_gradientPotential G).choose

theorem coeFn_gradientPotential (G : WeakSpatialGauge) :
    (G.gradientPotential.val : Position → Vector) =ᵐ[volume] G.gradientVector :=
  (exists_gradientPotential G).choose_spec

/-- The unshifted physical vector potential transforms by A minus grad theta. -/
def gaugeVector (G : WeakSpatialGauge) (A : VectorPotential) : VectorPotential :=
  A - G.gradientPotential

theorem coeFn_gaugeVector (G : WeakSpatialGauge) (A : VectorPotential) :
    ((G.gaugeVector A).val : Position → Vector) =ᵐ[volume]
      fun x => A.val x - G.gradientVector x := by
  have h : ((G.gaugeVector A).val : Position → Vector) =ᵐ[volume]
      fun x => A.val x - G.gradientPotential.val x :=
    AEEqFun.coeFn_sub A.val G.gradientPotential.val
  filter_upwards [h, G.coeFn_gradientPotential] with x hx hy
  rw [hx, hy]

@[simp] theorem zero_gaugeVector (A : VectorPotential) : zero.gaugeVector A = A := by
  apply sum_ext_ae
  filter_upwards [zero.coeFn_gaugeVector A] with x hx
  simpa only [zero_gradientVector, sub_zero] using hx

theorem neg_gaugeVector (G : WeakSpatialGauge) (A : VectorPotential) :
    G.neg.gaugeVector (G.gaugeVector A) = A := by
  apply sum_ext_ae
  filter_upwards [G.neg.coeFn_gaugeVector (G.gaugeVector A), G.coeFn_gaugeVector A]
    with x hx hy
  rw [hx, hy, neg_gradientVector]
  abel

theorem gaugeVector_neg (G : WeakSpatialGauge) (A : VectorPotential) :
    G.gaugeVector (G.neg.gaugeVector A) = A := by
  apply sum_ext_ae
  filter_upwards [G.coeFn_gaugeVector (G.neg.gaugeVector A), G.neg.coeFn_gaugeVector A]
    with x hx hy
  rw [hx, hy, neg_gradientVector]
  abel

theorem add_gaugeVector (G H : WeakSpatialGauge) (A : VectorPotential) :
    (G.add H).gaugeVector A = H.gaugeVector (G.gaugeVector A) := by
  apply sum_ext_ae
  filter_upwards [(G.add H).coeFn_gaugeVector A,
    H.coeFn_gaugeVector (G.gaugeVector A), G.coeFn_gaugeVector A] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, add_gradientVector]
  abel

end GptLean.TransformationsGauge.WeakSpatialGauge
