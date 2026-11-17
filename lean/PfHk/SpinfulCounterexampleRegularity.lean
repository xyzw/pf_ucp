import PfHk.SpinfulCounterexamplePotentials
import PfHk.CounterexampleMagneticField
import PfHk.PhysicalFermionicCoefficients
import PfHk.SpinfulCounterexampleMagnetic
import PfHk.PauliPhysicalLocalRegularity

/-! The explicit zero-coupling potentials meet the paper's local UCP
coefficient assumptions, and their actual potential classes are not gauge
equivalent for distinct parameters. -/

noncomputable section
namespace PfHk.SpinfulCounterexamplePotentials

open MeasureTheory Filter PfHk.SpinfulCounterexampleField
  PfHk.CounterexampleMagneticField PfHk.PhysicalFermionicCoefficients
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 300000

theorem vector_local_memLp (t : ℝ) (j : Fin 3) (p : ℝ≥0∞) (o : Space) (r : ℝ) :
    MemLp (fun x => (vector t).val x j) p (volume.restrict (Metric.ball o r)) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball o r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hv : MemLp (fun x => vectorPotential t x j) ∞ volume :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp_memLp' (vector_memLp_top t)
  apply ((hv.restrict (Metric.ball o r)).mono_exponent (p := p) le_top).ae_eq
  exact (ae_restrict_of_ae (vector_ae t)).mono fun x hx => congrArg (fun a : Space => a j) hx.symm

theorem scalar_local_memLp {p : ℝ} (hp : 0 < p) (hp3 : p < 3)
    (Z t : ℝ) (o : Space) (r : ℝ) :
    MemLp ((scalar Z t).val : Space → ℝ) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball o r)) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball o r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hsq : MemLp (fun x => ‖field x‖ ^ 2) ∞ volume := by
    apply (field_memLp_top.norm.mul field_memLp_top.norm).ae_eq
    exact ae_of_all _ fun x => by simp only [Pi.mul_apply, pow_two]
  have hb : MemLp (fun x => t ^ 2 / 2 * ‖field x‖ ^ 2) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball o r)) :=
    ((hsq.const_mul (t ^ 2 / 2)).restrict (Metric.ball o r)).mono_exponent le_top
  have hc := (CounterexamplePotentials.inverse_norm_memLp_ball hp hp3 o r).const_mul (-Z)
  have hv : MemLp (scalarPotential Z t) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball o r)) := by
    have hz := ((zeeman_memLp_top t).restrict (Metric.ball o r)).mono_exponent (p := ENNReal.ofReal p) le_top
    apply ((hc.sub hb).add hz).ae_eq
    exact ae_of_all _ fun x => by simp only [Pi.sub_apply, Pi.add_apply, scalarPotential, div_eq_mul_inv]
  apply hv.ae_eq
  filter_upwards [ae_restrict_of_ae (scalar_ae Z t)] with x hx
  exact hx.symm

theorem vector_weakDivergence (t : ℝ) :
    FriedrichsDivergenceBackground.WeakDivergence
      (fun j x => (vector t).val x j) (fun _ => 0) := by
  intro φ hφ hs
  calc
    (∫ x, (0 : ℝ) * φ x) = -(∑ j : Fin 3, ∫ x,
        vectorPotential t x j * fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
      SpinfulCounterexampleField.weakDivergence_vectorPotential t φ hφ hs
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [vector_ae t] with x hx
      rw [hx]

/-- The additional local regularity holds for every exponent between two
and three, including at the Coulomb singularity. -/
def regularityOfExponent (Z t p : ℝ) (hp : 2 < p) (hp3 : p < 3) :
    Regularity (vector t) (scalar Z t) where
  exponent := p
  exponent_gt_two := hp
  divergence := fun _ => 0
  vector_local := fun j o r _ => vector_local_memLp t j 6 o r
  scalar_local := fun o r _ => scalar_local_memLp (by linarith) hp3 Z t o r
  divergence_local := fun _ _ _ => MemLp.zero'
  weak_divergence := vector_weakDivergence t

/-- A fixed admissible choice of exponent for the HK regularity structure. -/
def regularity (Z t : ℝ) : Regularity (vector t) (scalar Z t) :=
  regularityOfExponent Z t (5 / 2) (by norm_num) (by norm_num)

theorem not_distributional_gauge_equivalent {s t : ℝ} (hst : s ≠ t) :
    ¬ IsDistributionalGradient (fun x => (vector t).val x - (vector s).val x) := by
  intro hg
  apply SpinfulCounterexampleField.not_distributional_gauge_equivalent hst
  apply hg.congr
  filter_upwards [vector_ae t, vector_ae s] with x ht hs
  rw [ht, hs]

theorem not_spatialGauge_equivalent {s t : ℝ} (hst : s ≠ t)
    (g : GptLean.TransformationsGauge.SpatialGauge) :
    ¬ ((fun x => (vector t).val x - (vector s).val x) =ᵐ[volume] g.gradientVector) := by
  intro he
  exact not_distributional_gauge_equivalent hst
    ((spatialGauge_isDistributionalGradient g).congr he.symm)

theorem vector_not_ae_eq {s t : ℝ} (hst : s ≠ t) :
    ¬ (((vector s).val : Space → Space) =ᵐ[volume] (vector t).val) := by
  intro hclasses
  have hae : vectorPotential s =ᵐ[volume] vectorPotential t :=
    (vector_ae s).symm.trans (hclasses.trans (vector_ae t))
  have hfun := Measure.eq_of_ae_eq hae (SpinfulCounterexampleField.contDiff_vectorPotential s).continuous
    (SpinfulCounterexampleField.contDiff_vectorPotential t).continuous
  exact distinct_magnetic_fields hst (congrArg curl hfun)

theorem vector_ne_of_ne {s t : ℝ} (hst : s ≠ t) : vector s ≠ vector t := by
  intro he
  apply vector_not_ae_eq hst
  rw [he]


/-- All local Pauli hypotheses, including distributional magnetic curl,
hold for each exponent strictly between two and three. -/
def pauliRegularityOfExponent (Z t p : ℝ) (hp : 2 < p) (hp3 : p < 3) :
    PauliPhysicalLocalRegularity.RegularityOn (vector t) (scalar Z t) Set.univ where
  exponent := p
  exponent_gt_two := hp
  divergence := fun _ => 0
  vector_local := by
    intro j K hK _
    obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Space)
    exact (vector_local_memLp t j 6 0 r).mono_measure (Measure.restrict_mono hr le_rfl)
  scalar_local := by
    intro K hK _
    obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Space)
    exact (scalar_local_memLp (by linarith) hp3 Z t 0 r).mono_measure
      (Measure.restrict_mono hr le_rfl)
  divergence_local := fun _ _ _ => MemLp.zero'
  weak_divergence := fun φ hφ hs _ => vector_weakDivergence t φ hφ hs
  magnetic := fun k x => curl (vectorPotential t) x k
  magnetic_local := by
    intro k K hK _
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact ((SpinfulCounterexampleMagnetic.curl_coordinate_memLp_top t k).restrict K).mono_exponent le_top
  weak_curl := by
    intro k φ hφ hs hsub
    have h := SpinfulCounterexampleMagnetic.weakCurl_vectorPotential t k φ hφ hs hsub
    refine h.trans ?_
    congr 1 <;> apply integral_congr_ae
    all_goals
      filter_upwards [vector_ae t] with x hx
      rw [hx]

def pauliRegularity (Z t : ℝ) :
    PauliPhysicalLocalRegularity.RegularityOn (vector t) (scalar Z t) Set.univ :=
  pauliRegularityOfExponent Z t (5 / 2) (by norm_num) (by norm_num)

end PfHk.SpinfulCounterexamplePotentials
