import GptLean.PhysicalPFFormEvaluation
import GptLean.Repair.ScalarFormOperations

/-!
Ordinary C1 representatives with compact support and an actual radiation
form graph give vectors in the actual free PF reference domain. This is
used to test the free variational operator after coordinate changes.
-/

noncomputable section
namespace PfHk.C1ReferenceCore

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPFFormEvaluation GptLean.PhotonLocalization GptLean.Repair GptLean.SymmetricLift
open scoped ENNReal Topology InnerProductSpace ContDiff
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

section Ordinary
variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

private theorem continuous_compact_memLp {f : EuclideanSpace ℝ I → H}
    (hf : Continuous f) {K : Set (EuclideanSpace ℝ I)} (hK : IsCompact K) :
    MemLp f 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable.restrict B
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hB x hx

private theorem continuous_test_integrable {f : EuclideanSpace ℝ I → H}
    (hf : Continuous f) {φ : EuclideanSpace ℝ I → ℝ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable (fun x => φ x • f x) :=
  integrable_smul_of_memLp_on_support
    ((hφ.memLp_of_hasCompactSupport hs).restrict (tsupport φ))
    (continuous_compact_memLp hf hs) (fun x hx => image_eq_zero_of_notMem_tsupport hx)

/-- The existing smooth weak derivative proof needs only one continuous derivative. -/
theorem weakH1Local_of_contDiff_one {f : EuclideanSpace ℝ I → H}
    (hf : ContDiff ℝ (1 : ℕ∞) f) :
    HasWeakH1Local f (fun i x => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  have hd (i : I) : Continuous (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨fun _ hK => continuous_compact_memLp hf.continuous hK,
    fun i _ hK => continuous_compact_memLp (hd i) hK, ?_⟩
  intro i φ hφ hs
  have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (continuous_test_integrable hf.continuous hdφ (hs.fderiv_apply ℝ _))
    (continuous_test_integrable (hd i) hφ.continuous hs)
    (continuous_test_integrable hf.continuous hφ.continuous hs)
    (fun x _ => hφ.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)

end Ordinary

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The actual representative furnished by a radiation graph valued function. -/
def valueFunction (q : Position I → RadiationGraphSpace) (x : Position I) : PhotonFock :=
  radiationGraphInclusion (q x)

def derivativeFunction (q : Position I → RadiationGraphSpace) (i : I) (x : Position I) : PhotonFock :=
  fderiv ℝ (valueFunction q) x (EuclideanSpace.single i 1)

theorem value_memLp (q : Position I → RadiationGraphSpace) (hq : MemLp q 2 volume) :
    MemLp (valueFunction q) 2 volume := radiationGraphInclusion.comp_memLp' hq

theorem derivative_memLp (q : Position I → RadiationGraphSpace)
    (hf : ContDiff ℝ (1 : ℕ∞) (valueFunction q)) (hs : HasCompactSupport (valueFunction q)) (i : I) :
    MemLp (derivativeFunction q i) 2 volume :=
  ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hs.fderiv_apply ℝ (EuclideanSpace.single i 1))

def freeVector (q : Position I → RadiationGraphSpace) (hq : MemLp q 2 volume)
    (hf : ContDiff ℝ (1 : ℕ∞) (valueFunction q)) (hs : HasCompactSupport (valueFunction q)) :
    SpatialFreeVector (I := I) radiationRoot where
  value := (value_memLp q hq).toLp (valueFunction q)
  derivative i := (derivative_memLp q hf hs i).toLp (derivativeFunction q i)
  radiation := (radiationGraphDerivative.comp_memLp' hq).toLp (fun x => radiationGraphDerivative (q x))
  weak := (weakH1Local_of_contDiff_one hf).congr (value_memLp q hq).coeFn_toLp.symm
    (fun i => (derivative_memLp q hf hs i).coeFn_toLp.symm)
  radiation_graph := by
    filter_upwards [(value_memLp q hq).coeFn_toLp,
      (radiationGraphDerivative.comp_memLp' hq).coeFn_toLp] with x hx hr
    have hr' : (radiationGraphDerivative.comp_memLp' hq).toLp
        (fun x => radiationGraphDerivative (q x)) x = radiationGraphDerivative (q x) := by
      convert! hr using 1
    rw [hx, hr']
    exact (q x).property

private theorem zero_potential_relation (v : SpatialFreeVector (I := I) radiationRoot) :
    ∀ᵐ x ∂volume, (0 : WaveSpace I) x = (Real.sqrt (0 : ℝ) : ℂ) • v.value x := by
  filter_upwards [Lp.coeFn_zero PhotonFock 2 (volume : Measure (Position I))] with x hx
  simp only [hx, Pi.zero_apply, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]

/-- Concrete free Reference realization. The only hypotheses are ordinary
C1 regularity, compact support, and L2 integrability of the actual graph. -/
def reference (q : Position I → RadiationGraphSpace) (hq : MemLp q 2 volume)
    (hf : ContDiff ℝ (1 : ℕ∞) (valueFunction q)) (hs : HasCompactSupport (valueFunction q)) :
    Reference I (fun _ => 0) :=
  referenceOfFree I (fun _ => 0) (freeVector q hq hf hs) 0 (zero_potential_relation _)

theorem reference_value (q : Position I → RadiationGraphSpace) (hq : MemLp q 2 volume)
    (hf : ContDiff ℝ (1 : ℕ∞) (valueFunction q)) (hs : HasCompactSupport (valueFunction q)) :
    inclusion I (fun _ => 0) (reference q hq hf hs) =
      (value_memLp q hq).toLp (valueFunction q) := rfl

theorem reference_ordinary (q : Position I → RadiationGraphSpace) (hq : MemLp q 2 volume)
    (hf : ContDiff ℝ (1 : ℕ∞) (valueFunction q)) (hs : HasCompactSupport (valueFunction q)) (i : I) :
    ordinary I (fun _ => 0) i (reference q hq hf hs) =
      (derivative_memLp q hf hs i).toLp (derivativeFunction q i) := rfl

theorem reference_radiation (q : Position I → RadiationGraphSpace) (hq : MemLp q 2 volume)
    (hf : ContDiff ℝ (1 : ℕ∞) (valueFunction q)) (hs : HasCompactSupport (valueFunction q)) :
    radiation I (fun _ => 0) (reference q hq hf hs) =
      (radiationGraphDerivative.comp_memLp' hq).toLp (fun x => radiationGraphDerivative (q x)) :=
  referenceOfFree_radiation I (fun _ => 0) (freeVector q hq hf hs) 0 (zero_potential_relation _)

theorem reference_potential (q : Position I → RadiationGraphSpace) (hq : MemLp q 2 volume)
    (hf : ContDiff ℝ (1 : ℕ∞) (valueFunction q)) (hs : HasCompactSupport (valueFunction q)) :
    potential I (fun _ => 0) (reference q hq hf hs) = 0 := rfl

end PfHk.C1ReferenceCore
