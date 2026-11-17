import PfHk.PauliMagnetizationDistribution
import PfHk.PauliCurrentGroundState
import GptLean.PhysicalPFCovariantSymmetry

/-! Identification of the physical Pauli velocity current with the
orbital current and one half of the spin magnetization curl. Field
reality is derived from the actual photon field on its radiation domain. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliCurrentPhysicalCorrection

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.PauliSpin PfHk.PauliCurrentAlgebra
  PfHk.PauliCurrentCorrection

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] referenceSubspace inclusion radiationSource
  PhysicalPFReference.field covariant ordinary
  radiationGraphInclusion kernelField

private theorem subtract_smul {H : Type*} [AddCommGroup H] [Module ℂ H]
    (d f : H) (e : ℝ) :
    (-Complex.I) • d - (e : ℂ) • f =
      (-Complex.I) • d + (-(e : ℂ)) • f := by
  simp only [sub_eq_add_neg, neg_smul]

variable {N : ℕ}

local instance pauliPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }
local instance pauliWaveDirectInner : InnerProductSpace ℂ (WaveSpace (Fin N × Fin 3)) :=
  { (inferInstance : InnerProductSpace ℂ (WaveSpace (Fin N × Fin 3))) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (WaveSpace (Fin N × Fin 3))) }

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hb : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M)

theorem field_symmetric_ae (q : Fin N × Fin 3)
    (u v : Reference (Fin N × Fin 3) (fun _ => 0)) :
    ∀ᵐ X ∂volume,
      inner ℂ (E := PhotonFock) (PhysicalPFReference.field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb q u X)
        (inclusion (Fin N × Fin 3) (fun _ => 0) v X) =
      inner ℂ (E := PhotonFock) (inclusion (Fin N × Fin 3) (fun _ => 0) u X)
        (PhysicalPFReference.field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb q v X) := by
  have hi (w : Reference (Fin N × Fin 3) (fun _ => 0)) :
      (inclusion (Fin N × Fin 3) (fun _ => 0) w : Configuration N → PhotonFock) =ᵐ[volume]
        fun X => radiationGraphInclusion (radiationSource (Fin N × Fin 3) (fun _ => 0) w X) :=
    (Filter.EventuallyEq.of_eq (congrArg (fun f : WaveSpace (Fin N × Fin 3) => fun X : Configuration N => f X)
      (radiation_matches (Fin N × Fin 3) (fun _ => 0) w).symm)).trans
      (radiationGraphInclusion.coeFn_compLpL (radiationSource (Fin N × Fin 3) (fun _ => 0) w))
  have hf (w : Reference (Fin N × Fin 3) (fun _ => 0)) :
      (PhysicalPFReference.field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb q w :
        Configuration N → PhotonFock) =ᵐ[volume]
      fun X => kernelField C (κ q X) (radiationSource (Fin N × Fin 3) (fun _ => 0) w X) := by
    unfold PhysicalPFReference.field
    exact spatialField_ae (X := Configuration N) volume C (κ q) (hκ q) M (hb q)
      (radiationSource (Fin N × Fin 3) (fun _ => 0) w)
  filter_upwards [hi u, hi v, hf u, hf v] with X hiu hiv hfu hfv
  exact (congrArg₂ (inner ℂ (E := PhotonFock)) hfu hiv).trans
    ((kernelField_symmetric C (κ q X) _ _).trans
      (congrArg₂ (inner ℂ (E := PhotonFock)) hiu.symm hfv.symm))

theorem covariant_ae (e : ℝ) (q : Fin N × Fin 3)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    ∀ᵐ X ∂volume,
      covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e q u X =
      (-Complex.I) • ordinary (Fin N × Fin 3) (fun _ => 0) q u X +
        (-(e : ℂ)) • PhysicalPFReference.field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb q u X := by
  let d : WaveSpace (Fin N × Fin 3) := ordinary (Fin N × Fin 3) (fun _ => 0) q u
  let f : WaveSpace (Fin N × Fin 3) :=
    PhysicalPFReference.field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb q u
  have he : covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e q u =
      (-Complex.I) • d - (e : ℂ) • f :=
    PhysicalPFReference.covariant_apply (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e q u
  filter_upwards [Lp.coeFn_sub ((-Complex.I) • d) ((e : ℂ) • f),
    Lp.coeFn_smul (-Complex.I) d, Lp.coeFn_smul (e : ℂ) f] with X hsub hd hf
  change ((-Complex.I) • d - (e : ℂ) • f) X =
    ((-Complex.I) • d) X - ((e : ℂ) • f) X at hsub
  change ((-Complex.I) • d) X = (-Complex.I) • d X at hd
  change ((e : ℂ) • f) X = (e : ℂ) • f X at hf
  exact (congrArg (fun w : WaveSpace (Fin N × Fin 3) => w X) he).trans
    (hsub.trans ((congrArg₂ (fun a b : PhotonFock => a - b) hd hf).trans
      (subtract_smul (d X) (f X) e)))

theorem current_correction_ae (e : ℝ) (u : PauliReference.Ref N)
    (n : Fin N) (a : Fin 3) :
    ∀ᵐ X ∂volume,
      current (N := N) (H := PhotonFock) n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
        (fun b s => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e (n,b) (u s) X) a =
      orbitalCurrent (N := N) (H := PhotonFock) (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
        (fun b s => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e (n,b) (u s) X) a +
      (1 / 2 : ℝ) * magnetizationCurl (N := N) (H := PhotonFock) n
        (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
        (fun b s => ordinary (Fin N × Fin 3) (fun _ => 0) (n,b) (u s) X) a := by
  filter_upwards [ae_all_iff.mpr (fun b : Fin 3 => ae_all_iff.mpr
      (fun s => covariant_ae C κ hκ M hb e (n,b) (u s))),
    ae_all_iff.mpr (fun b : Fin 3 => ae_all_iff.mpr (fun s => ae_all_iff.mpr
      (fun t => field_symmetric_ae C κ hκ M hb (n,b) (u s) (u t))))] with X hd hf
  have he : (fun b s => covariant (Fin N × Fin 3) (fun _ => 0)
      C κ hκ M hb e (n,b) (u s) X) =
      covariantDerivative (N := N) (H := PhotonFock) e
        (fun b s => ordinary (Fin N × Fin 3) (fun _ => 0) (n,b) (u s) X)
        (fun b s => PhysicalPFReference.field (Fin N × Fin 3) (fun _ => 0)
          C κ hκ M hb (n,b) (u s) X) := funext fun b => funext fun s => hd b s
  exact (congrArg (fun d : Fin 3 → SpinIndex N → PhotonFock =>
    current (N := N) (H := PhotonFock) n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) d a) he).trans
      ((current_correction (N := N) (H := PhotonFock) n _ e _ _
        (fun b k => spinPair_im_of_symmetric (N := N) (H := PhotonFock) n _ _ (hf b) k) a).trans
          (congrArg (fun d : Fin 3 → SpinIndex N → PhotonFock =>
            orbitalCurrent (N := N) (H := PhotonFock) (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) d a +
              (1 / 2 : ℝ) * magnetizationCurl (N := N) (H := PhotonFock) n
                (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
                (fun b s => ordinary (Fin N × Fin 3) (fun _ => 0) (n,b) (u s) X) a) he.symm))

end PfHk.PauliCurrentPhysicalCorrection

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
