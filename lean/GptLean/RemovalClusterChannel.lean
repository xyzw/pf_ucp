import GptLean.RemovalClusterMeasured
import GptLean.RemovalLift

/-! The concrete cluster field is inserted into the actual measurable
repair tag and countable lift. Product-measure claims are obtained from
measurable predicates and the proved spatial statements at each parameter. -/

noncomputable section

set_option maxHeartbeats 1000000

namespace GptLean.RemovalGeometry

open Finset MeasureTheory MeasureTheory.Measure Filter GptLean.Repair GptLean.SymmetricLift
open scoped ContDiff

variable {N : ℕ} {Q ι : Type*} [MeasurableSpace Q]

def clusterTag (c : Fin N → ClusterSpace) (R e : ℝ) (Z : Q → ℝ)
    (a : Q → ClusterSpace → ClusterSpace) (q : Q) : RepairSpace → SixTag :=
  repairTag (clusterVelocityBound N R e (Z q)) (clusterJacobianBound N e (Z q))
    (piCoordinateField (clusterResidual c R e (a q)))

def clusterTagGradient (c : Fin N → ClusterSpace) (R e : ℝ) (Z : Q → ℝ)
    (a : Q → ClusterSpace → ClusterSpace) (q : Q) : Fin 3 → RepairSpace → SixTag :=
  repairTagGradient (clusterVelocityBound N R e (Z q)) (clusterJacobianBound N e (Z q))
    (piCoordinateField (clusterResidual c R e (a q)))

theorem clusterTag_properties (c : Fin N → ClusterSpace) {R e : ℝ}
    (hR : 0 < R) (he : 0 ≤ e) {Z : Q → ℝ} (hZ : ∀ q, 0 ≤ Z q)
    {a : Q → ClusterSpace → ClusterSpace} (ha : ∀ q, ContDiff ℝ ∞ (a q))
    (hbound : ∀ q s, ∀ y ∈ Metric.ball (physicalClusterCentre c R s) (clusterRadius N R),
      ‖fderiv ℝ (a q) y‖ ≤ Z q) (q : Q) :
    HasWeakH1Local (clusterTag c R e Z a q) (clusterTagGradient c R e Z a q) ∧
    (∀ y, ‖clusterTag c R e Z a q y‖ = 1) ∧
    (∀ j y, inner ℂ (clusterTag c R e Z a q y) (clusterTagGradient c R e Z a q j y) =
      Complex.I * (clusterResidual c R e (a q) y j : ℂ)) := by
  obtain ⟨hv, hvV, hdv⟩ := clusterResidual_pi_bounds c hR he (hZ q) (ha q) (hbound q)
  have hV := clusterVelocityBound_nonneg N hR.le he (hZ q)
  have hM := clusterJacobianBound_nonneg N he (hZ q)
  refine ⟨selectedTag_hasWeakH1Local_of_differentiable hV hM hv hvV hdv, ?_, ?_⟩
  · intro y
    exact selectedTag_norm _ _ _ hV (WithLp.ofLp y) (hvV (WithLp.ofLp y))
  · intro j y
    exact selectedTag_connection hV (hvV (WithLp.ofLp y))
      (fun i l => hasDerivAt_pi.mp
        ((hv (WithLp.ofLp y)).hasFDerivAt.hasLineDerivAt (Pi.single l (1 : ℝ))) i) j

theorem clusterTag_jointly_stronglyMeasurable (c : Fin N → ClusterSpace) (R e : ℝ)
    {Z : Q → ℝ} (hZ : Measurable Z) {a : Q → ClusterSpace → ClusterSpace}
    (ha : StronglyMeasurable (Function.uncurry a)) :
    StronglyMeasurable (Function.uncurry (clusterTag c R e Z a)) := by
  have hV : Measurable (fun q => clusterVelocityBound N R e (Z q)) := by
    unfold clusterVelocityBound
    fun_prop
  have hM : Measurable (fun q => clusterJacobianBound N e (Z q)) := by
    unfold clusterJacobianBound
    fun_prop
  have hv : StronglyMeasurable (Function.uncurry
      (fun q x => WithLp.ofLp (clusterResidual c R e (a q) x))) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp_stronglyMeasurable
      (clusterResidual_jointly_stronglyMeasurable c R e ha)
  exact selectedTag_jointly_stronglyMeasurable
    (v := fun q x => WithLp.ofLp (clusterResidual c R e (a q) x)) hV hM hv

theorem clusterTagGradient_jointly_stronglyMeasurable
    (c : Fin N → ClusterSpace) {R e : ℝ} (hR : 0 < R) (he : 0 ≤ e)
    {Z : Q → ℝ} (hZmeas : Measurable Z) (hZ : ∀ q, 0 ≤ Z q)
    {a : Q → ClusterSpace → ClusterSpace} (ha : StronglyMeasurable (Function.uncurry a))
    (hd : ∀ q, ContDiff ℝ ∞ (a q))
    (hda : ∀ j : Fin 3, StronglyMeasurable (fun p : Q × ClusterSpace =>
      fderiv ℝ (a p.1) p.2 (EuclideanSpace.single j (1 : ℝ))))
    (hbound : ∀ q s, ∀ y ∈ Metric.ball (physicalClusterCentre c R s) (clusterRadius N R),
      ‖fderiv ℝ (a q) y‖ ≤ Z q) (j : Fin 3) :
    StronglyMeasurable (Function.uncurry (fun q => clusterTagGradient c R e Z a q j)) := by
  have hV : Measurable (fun q => clusterVelocityBound N R e (Z q)) := by
    unfold clusterVelocityBound
    fun_prop
  have hM : Measurable (fun q => clusterJacobianBound N e (Z q)) := by
    unfold clusterJacobianBound
    fun_prop
  let v : Q → ClusterSpace → Fin 3 → ℝ := fun q x => WithLp.ofLp (clusterResidual c R e (a q) x)
  let dv : Q → ClusterSpace → Fin 3 → Fin 3 → ℝ := fun q x i l =>
    fderiv ℝ (clusterResidual c R e (a q)) x (EuclideanSpace.single l (1 : ℝ)) i
  have hv : StronglyMeasurable (Function.uncurry v) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp_stronglyMeasurable
      (clusterResidual_jointly_stronglyMeasurable c R e ha)
  have hdv : StronglyMeasurable (Function.uncurry dv) := by
    apply Measurable.stronglyMeasurable
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro l
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp_stronglyMeasurable
      (clusterResidual_derivative_jointly_stronglyMeasurable c R e ha
        (fun q => (hd q).differentiable (by simp)) hda l)).measurable
  have hvV : ∀ q x i, |v q x i| ≤ clusterVelocityBound N R e (Z q) := by
    intro q x i
    have h := (PiLp.norm_apply_le (clusterResidual c R e (a q) x) i).trans
      (norm_clusterResidual_le c hR he (hZ q) ((hd q).differentiable (by simp)) (hbound q) x)
    simpa only [v, Real.norm_eq_abs, clusterVelocityBound] using h
  have hderiv : ∀ q x i l, HasDerivAt
      (fun s : ℝ => v q (x + s • EuclideanSpace.single l 1) i) (dv q x i l) 0 := by
    intro q x i l
    have h := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (clusterResidual c R e (a q) x) i).comp x
      (((clusterResidual_contDiff c R e (hd q)).differentiable (by simp) x).hasFDerivAt)
    exact h.hasLineDerivAt (EuclideanSpace.single l 1)
  exact selectedTagDerivative_jointly_stronglyMeasurable hV hM hv hdv
    (fun q => clusterVelocityBound_nonneg N hR.le he (hZ q)) hvV hderiv j

def clusterChannelLift (B : TensorBackground SixTag)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    (c : Fin N → ClusterSpace) (R e : ℝ) (Z : Q → ℝ) (a : Q → ClusterSpace → ClusterSpace) :
    Q → Configuration N → CountableTarget :=
  measuredRepairLift B N basis index (clusterTag c R e Z a)

def clusterChannelGradient (B : TensorBackground SixTag)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    (c : Fin N → ClusterSpace) (R e : ℝ) (Z : Q → ℝ) (a : Q → ClusterSpace → ClusterSpace) :
    (Fin N × Fin 3) → Q → Configuration N → CountableTarget :=
  measuredRepairGradient B N basis index (clusterTag c R e Z a) (clusterTagGradient c R e Z a)

theorem clusterChannel_properties (B : TensorBackground SixTag) (T : TensorMultilinearData B)
    (basis : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target) (index : ι ↪ ℕ)
    (c : Fin N → ClusterSpace) {R e : ℝ} (hR : 0 < R) (he : 0 ≤ e)
    (μ : Measure Q) {Z : Q → ℝ} (hZmeas : Measurable Z) (hZ : ∀ q, 0 ≤ Z q)
    {a : Q → ClusterSpace → ClusterSpace} (ha : StronglyMeasurable (Function.uncurry a))
    (hd : ∀ q, ContDiff ℝ ∞ (a q))
    (hda : ∀ j : Fin 3, StronglyMeasurable (fun p : Q × ClusterSpace =>
      fderiv ℝ (a p.1) p.2 (EuclideanSpace.single j (1 : ℝ))))
    (hbound : ∀ q s, ∀ y ∈ Metric.ball (physicalClusterCentre c R s) (clusterRadius N R),
      ‖fderiv ℝ (a q) y‖ ≤ Z q) :
    let z := clusterChannelLift B basis index c R e Z a
    let dz := clusterChannelGradient B basis index c R e Z a
    StronglyMeasurable (Function.uncurry z) ∧
    (∀ j, StronglyMeasurable (Function.uncurry (dz j))) ∧
    (∀ q, HasWeakH1Local (z q) (fun j => dz j q)) ∧
    (∀ᵐ p ∂μ.prod volume, ‖z p.1 p.2‖ = 1) ∧
    (∀ j, ∀ᵐ p ∂μ.prod volume, inner ℂ (z p.1 p.2) (dz j p.1 p.2) =
      Complex.I * (clusterResidual c R e (a p.1) (particle p.2 j.1) j.2 : ℂ)) ∧
    (∀ᵐ p ∂μ.prod volume, (∑ j, ‖dz j p.1 p.2‖ ^ 2) ≤
      2 * clusterRepairMetricConstant N * (e ^ 2 * R ^ 2 * Z p.1 ^ 2 + e * Z p.1)) := by
  let t := clusterTag c R e Z a
  let g := clusterTagGradient c R e Z a
  let z := clusterChannelLift B basis index c R e Z a
  let dz := clusterChannelGradient B basis index c R e Z a
  have ht : StronglyMeasurable (Function.uncurry t) :=
    clusterTag_jointly_stronglyMeasurable c R e hZmeas ha
  have hg : ∀ j, StronglyMeasurable (Function.uncurry (fun q => g q j)) :=
    clusterTagGradient_jointly_stronglyMeasurable c hR he hZmeas hZ ha hd hda hbound
  have hp (q) := clusterTag_properties c hR he hZ hd hbound q
  have hz : StronglyMeasurable (Function.uncurry z) :=
    measuredRepairLift_stronglyMeasurable B T N basis index ht
  have hdz (j) : StronglyMeasurable (Function.uncurry (dz j)) :=
    measuredRepairGradient_stronglyMeasurable B T N basis index ht hg j
  refine ⟨hz, hdz, fun q => measuredRepairLift_weak B T N basis index q (hp q).1 (hp q).2.1,
    ?_, ?_, ?_⟩
  · apply (ae_prod_iff_ae_ae (measurableSet_eq_fun hz.norm.measurable measurable_const)).mpr
    exact Eventually.of_forall fun q => measuredRepairLift_unit B N basis index q (hp q).2.1
  · intro j
    have hs : StronglyMeasurable (fun p : Q × Configuration N =>
        clusterResidual c R e (a p.1) (particle p.2 j.1) j.2) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j.2).continuous.comp_stronglyMeasurable
        ((clusterResidual_jointly_stronglyMeasurable c R e ha).comp_measurable
          (measurable_fst.prodMk
            ((particleLinear j.1).toContinuousLinearMap.continuous.measurable.comp measurable_snd)))
    apply (ae_prod_iff_ae_ae (measurableSet_eq_fun (hz.inner (hdz j)).measurable
      (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hs.measurable)))).mpr
    exact Eventually.of_forall fun q => measuredRepairLift_connection B T N basis index
      (t := t) (g := g) (s := fun q l y => clusterResidual c R e (a q) y l) q
      (hp q).2.1 (hp q).2.2 j
  · have hm : Measurable (fun p : Q × Configuration N => ∑ j, ‖dz j p.1 p.2‖ ^ 2) :=
      (Finset.stronglyMeasurable_fun_sum Finset.univ (fun j _ => (hdz j).norm.pow 2)).measurable
    apply (ae_prod_iff_ae_ae (measurableSet_le hm (by fun_prop))).mpr
    apply Eventually.of_forall
    intro q
    filter_upwards [liftGradientRepresentative_ae_eq B N t g,
      cluster_repairLift_metric_paper B T c hR he (hZ q) (hd q) (hbound q)] with x hx hm
    simpa only [dz, clusterChannelGradient, measuredRepairGradient, countableEmbedding_norm,
      t, g, clusterTag, clusterTagGradient, hx] using hm

end GptLean.RemovalGeometry
