import GptLean.RemovalClusterRepair
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

/-! Parameter measurability of the concrete cluster construction. The
parameter space needs only a measurable structure. Every finite sum uses
fixed cutoffs and anchors, together with the supplied Gaussian field and
its three measured spatial derivative vectors. -/

noncomputable section

set_option maxHeartbeats 800000

namespace GptLean.RemovalGeometry

open Finset MeasureTheory GptLean.Repair
open scoped ContDiff InnerProductSpace

variable {N : ℕ} {Q : Type*} [MeasurableSpace Q]

local instance (G : SimpleGraph (Fin N)) : DecidableEq G.ConnectedComponent := Classical.decEq _
local instance (G : SimpleGraph (Fin N)) : Fintype G.ConnectedComponent := Fintype.ofFinite _

theorem clusterPhase_jointly_stronglyMeasurable (c : Fin N → ClusterSpace) (R e : ℝ)
    {a : Q → ClusterSpace → ClusterSpace} (ha : StronglyMeasurable (Function.uncurry a)) :
    StronglyMeasurable (Function.uncurry (fun q => clusterPhase c R e (a q))) := by
  have hs : StronglyMeasurable (fun p : Q × ClusterSpace =>
      ∑ s : (clusterGraph c R).ConnectedComponent, physicalClusterCutoff c R s p.2 *
        inner ℝ (a p.1 (physicalClusterCentre c R s)) (p.2 - physicalClusterCentre c R s)) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro s _
    have hθ : StronglyMeasurable (fun p : Q × ClusterSpace => physicalClusterCutoff c R s p.2) :=
      (physicalClusterCutoff_contDiff c R s).continuous.comp_stronglyMeasurable
        measurable_snd.stronglyMeasurable
    have hac : StronglyMeasurable (fun p : Q × ClusterSpace => a p.1 (physicalClusterCentre c R s)) :=
      ha.comp_measurable (measurable_fst.prodMk measurable_const)
    exact hθ.mul (hac.inner (measurable_snd.stronglyMeasurable.sub stronglyMeasurable_const))
  exact hs.const_mul (-e)

theorem clusterResidual_jointly_stronglyMeasurable (c : Fin N → ClusterSpace) (R e : ℝ)
    {a : Q → ClusterSpace → ClusterSpace} (ha : StronglyMeasurable (Function.uncurry a)) :
    StronglyMeasurable (Function.uncurry (fun q => clusterResidual c R e (a q))) := by
  have hs : StronglyMeasurable (fun p : Q × ClusterSpace =>
      ∑ s : (clusterGraph c R).ConnectedComponent, physicalClusterCutoff c R s p.2 •
        (a p.1 p.2 - a p.1 (physicalClusterCentre c R s))) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro s _
    have hθ : StronglyMeasurable (fun p : Q × ClusterSpace => physicalClusterCutoff c R s p.2) :=
      (physicalClusterCutoff_contDiff c R s).continuous.comp_stronglyMeasurable
        measurable_snd.stronglyMeasurable
    exact hθ.smul (ha.sub (ha.comp_measurable (measurable_fst.prodMk measurable_const)))
  exact hs.const_smul (-e)

theorem clusterResidual_fderiv_apply (c : Fin N → ClusterSpace) (R e : ℝ)
    {a : ClusterSpace → ClusterSpace} (ha : Differentiable ℝ a) (x v : ClusterSpace) :
    fderiv ℝ (clusterResidual c R e a) x v =
      (-e) • ∑ s : (clusterGraph c R).ConnectedComponent,
        (physicalClusterCutoff c R s x • fderiv ℝ a x v +
          (fderiv ℝ (physicalClusterCutoff c R s) x v) •
            (a x - a (physicalClusterCentre c R s))) := by
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ)
    (A := fun s y => physicalClusterCutoff c R s y • (a y - a (physicalClusterCentre c R s)))
    (A' := fun s => physicalClusterCutoff c R s x • fderiv ℝ a x +
      (fderiv ℝ (physicalClusterCutoff c R s) x).smulRight (a x - a (physicalClusterCentre c R s)))
    (fun s _ => ((physicalClusterCutoff_contDiff c R s).differentiable (by simp) x).hasFDerivAt.fun_smul
      ((ha x).hasFDerivAt.sub_const (a (physicalClusterCentre c R s))))).const_smul (-e)
  change HasFDerivAt (clusterResidual c R e a) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply]

theorem clusterResidual_derivative_jointly_stronglyMeasurable
    (c : Fin N → ClusterSpace) (R e : ℝ) {a : Q → ClusterSpace → ClusterSpace}
    (ha : StronglyMeasurable (Function.uncurry a))
    (hd : ∀ q, Differentiable ℝ (a q))
    (hda : ∀ j : Fin 3, StronglyMeasurable (fun p : Q × ClusterSpace =>
      fderiv ℝ (a p.1) p.2 (EuclideanSpace.single j (1 : ℝ)))) (j : Fin 3) :
    StronglyMeasurable (fun p : Q × ClusterSpace =>
      fderiv ℝ (clusterResidual c R e (a p.1)) p.2 (EuclideanSpace.single j (1 : ℝ))) := by
  have hs : StronglyMeasurable (fun p : Q × ClusterSpace =>
      ∑ s : (clusterGraph c R).ConnectedComponent,
        (physicalClusterCutoff c R s p.2 • fderiv ℝ (a p.1) p.2 (EuclideanSpace.single j (1 : ℝ)) +
          (fderiv ℝ (physicalClusterCutoff c R s) p.2 (EuclideanSpace.single j (1 : ℝ))) •
            (a p.1 p.2 - a p.1 (physicalClusterCentre c R s)))) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro s _
    have hθ : StronglyMeasurable (fun p : Q × ClusterSpace => physicalClusterCutoff c R s p.2) :=
      (physicalClusterCutoff_contDiff c R s).continuous.comp_stronglyMeasurable
        measurable_snd.stronglyMeasurable
    have hdθ : Continuous (fun x => fderiv ℝ (physicalClusterCutoff c R s) x
        (EuclideanSpace.single j (1 : ℝ))) :=
      ((physicalClusterCutoff_contDiff c R s).continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hθ.smul (hda j)).add
      ((hdθ.comp_stronglyMeasurable measurable_snd.stronglyMeasurable).smul
        (ha.sub (ha.comp_measurable (measurable_fst.prodMk measurable_const))))
  convert hs.const_smul (-e) using 1
  funext p
  exact clusterResidual_fderiv_apply c R e (hd p.1) p.2 _

theorem piCoordinateField_jointly_stronglyMeasurable
    {v : Q → ClusterSpace → ClusterSpace} (hv : StronglyMeasurable (Function.uncurry v)) :
    StronglyMeasurable (Function.uncurry (fun q => piCoordinateField (v q))) := by
  have hto : Measurable (fun p : Q × (Fin 3 → ℝ) => (p.1, WithLp.toLp 2 p.2)) :=
    measurable_fst.prodMk
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.measurable.comp measurable_snd)
  exact (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp_stronglyMeasurable
    (hv.comp_measurable hto)

theorem piCoordinateField_derivative_jointly_stronglyMeasurable
    {v : Q → ClusterSpace → ClusterSpace} (hv : ∀ q, Differentiable ℝ (v q))
    (hdv : ∀ j : Fin 3, StronglyMeasurable (fun p : Q × ClusterSpace =>
      fderiv ℝ (v p.1) p.2 (EuclideanSpace.single j (1 : ℝ)))) (j : Fin 3) :
    StronglyMeasurable (fun p : Q × (Fin 3 → ℝ) =>
      fderiv ℝ (piCoordinateField (v p.1)) p.2 (Pi.single j (1 : ℝ))) := by
  have hto : Measurable (fun p : Q × (Fin 3 → ℝ) => (p.1, WithLp.toLp 2 p.2)) :=
    measurable_fst.prodMk
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.measurable.comp measurable_snd)
  have h := (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp_stronglyMeasurable
    ((hdv j).comp_measurable hto)
  convert h using 1
  funext p i
  exact piCoordinateField_fderiv (hv p.1) p.2 i j

theorem clusterResidual_pi_jointly_stronglyMeasurable
    (c : Fin N → ClusterSpace) (R e : ℝ) {a : Q → ClusterSpace → ClusterSpace}
    (ha : StronglyMeasurable (Function.uncurry a))
    (hd : ∀ q, ContDiff ℝ ∞ (a q))
    (hda : ∀ j : Fin 3, StronglyMeasurable (fun p : Q × ClusterSpace =>
      fderiv ℝ (a p.1) p.2 (EuclideanSpace.single j (1 : ℝ)))) :
    StronglyMeasurable (Function.uncurry (fun q => piCoordinateField (clusterResidual c R e (a q)))) ∧
    (∀ j : Fin 3, StronglyMeasurable (fun p : Q × (Fin 3 → ℝ) =>
      fderiv ℝ (piCoordinateField (clusterResidual c R e (a p.1))) p.2 (Pi.single j (1 : ℝ)))) := by
  refine ⟨piCoordinateField_jointly_stronglyMeasurable
    (clusterResidual_jointly_stronglyMeasurable c R e ha), ?_⟩
  intro j
  exact piCoordinateField_derivative_jointly_stronglyMeasurable
    (fun q => (clusterResidual_contDiff c R e (hd q)).differentiable (by simp))
    (clusterResidual_derivative_jointly_stronglyMeasurable c R e ha
      (fun q => (hd q).differentiable (by simp)) hda) j

end GptLean.RemovalGeometry
