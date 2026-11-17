import GptLean.ElectronicH1Reindex
import GptLean.NormWeakH1

/-! Transport the proved scalar norm chain rule from `Fin d` to an arbitrary
finite coordinate index, including the physical particle-coordinate pairs. -/

noncomputable section
namespace PfHk.NormWeakH1Finite

open MeasureTheory GptLean GptLean.SymmetricLift GptLean.ElectronicH1Space
open GptLean.ElectronicH1Reindex
open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option Elab.async false

variable {I J P : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [NormedAddCommGroup P] [CompleteSpace P]

/-- Coordinate transport for raw globally H1 representatives. -/
theorem weak_reindex [NormedSpace ℝ P] (e : I ≃ J)
    {f : EuclideanSpace ℝ I → P} {g : I → EuclideanSpace ℝ I → P}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hw : HasWeakH1Local f g) :
    HasWeakH1Local (fun x => f ((coordinates e).symm x))
      (fun j x => g (e.symm j) ((coordinates e).symm x)) := by
  let u : H1 P I := ⟨(hf.toLp f, fun i => (hg i).toLp (g i)),
    hw.congr hf.coeFn_toLp.symm (fun i => (hg i).coeFn_toLp.symm)⟩
  apply (weak_pull e u).congr
  · exact (pull_ae e (value u)).trans
      ((coordinates e).symm.measurePreserving.quasiMeasurePreserving.ae hf.coeFn_toLp)
  · intro j
    exact (pull_ae e (derivative (e.symm j) u)).trans
      ((coordinates e).symm.measurePreserving.quasiMeasurePreserving.ae (hg (e.symm j)).coeFn_toLp)

variable [InnerProductSpace ℝ P]

/-- The norm chain rule for an arbitrary finite coordinate index. Only
global L2 membership is added to the original local chain-rule hypotheses. -/
theorem norm_weakH1Local
    {f : EuclideanSpace ℝ I → P} {g : I → EuclideanSpace ℝ I → P}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hw : HasWeakH1Local f g) :
    HasWeakH1Local (fun x => ‖f x‖) (fun i x => ⟪f x, g i x⟫ / ‖f x‖) := by
  let e := Fintype.equivFin I
  let F : EuclideanSpace ℝ (Fin (Fintype.card I)) → P :=
    fun x => f ((coordinates e).symm x)
  let G : Fin (Fintype.card I) → EuclideanSpace ℝ (Fin (Fintype.card I)) → P :=
    fun i x => g (e.symm i) ((coordinates e).symm x)
  have hF : MemLp F 2 volume := hf.comp_measurePreserving (coordinates e).symm.measurePreserving
  have hG : ∀ i, MemLp (G i) 2 volume := fun i =>
    (hg (e.symm i)).comp_measurePreserving (coordinates e).symm.measurePreserving
  have hFG : HasWeakH1Local F G := weak_reindex e hf hg hw
  have hnorm := GptLean.NormWeakH1.norm_weakH1Local hFG
  have hgrad : ∀ i, MemLp (fun x => ⟪F x, G i x⟫ / ‖F x‖) 2 volume := by
    intro i
    apply (hG i).norm.mono'
      (((hF.aestronglyMeasurable.inner (hG i).aestronglyMeasurable).aemeasurable.div
        hF.aestronglyMeasurable.norm.aemeasurable).aestronglyMeasurable)
    exact ae_of_all _ fun x => GptLean.NormWeakH1.norm_inner_div_norm_le (F x) (G i x)
  have hback := weak_reindex e.symm hF.norm hgrad hnorm
  apply hback.congr
  · exact ae_of_all _ fun x => by
      simp only [F, ← coordinates_symm, LinearIsometryEquiv.symm_symm,
        LinearIsometryEquiv.symm_apply_apply]
  · intro i
    exact ae_of_all _ fun x => by
      simp only [F, G, ← coordinates_symm, LinearIsometryEquiv.symm_symm,
        LinearIsometryEquiv.symm_apply_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

end PfHk.NormWeakH1Finite
