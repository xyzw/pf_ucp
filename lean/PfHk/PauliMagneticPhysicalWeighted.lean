import PfHk.PauliMagneticOperator
import PfHk.PauliMagneticWeighted

/-! Weighted control of the actual L2 quantum Zeeman source. All pointwise
representatives and measurability properties are derived from the physical
radiation graph and the constructed spatial magnetic field. -/

noncomputable section
namespace PfHk.PauliMagneticPhysicalWeighted

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.PhysicalNonattainmentFluxKernel Gaussian
  GptLean.SymmetricLift GptLean.Representability
  PfHk.PhysicalFieldRegularity PfHk.PauliSpin

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [local irreducible] inclusion radiation radiationSource
  RadialGauge.momentBound PauliMagneticOperator.quantum

private theorem weighted_square_sum_congr {X S H : Type*} [MeasurableSpace X]
    [Fintype S] [NormedAddCommGroup H] (ν : Measure X) (w : X → ℝ)
    (f g : S → X → H) (h : ∀ s, f s =ᵐ[ν] g s) :
    (fun x => w x * ∑ s, ‖f s x‖ ^ 2) =ᵐ[ν]
      fun x => w x * ∑ s, ‖g s x‖ ^ 2 := by
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact congrArg (fun r : ℝ => w x * r)
    (Finset.sum_congr rfl (fun s _ => congrArg (fun z : H => ‖z‖ ^ 2) (hx s)))

private theorem transfer_bound {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {f f' r r' m m' : X → ℝ} {K a b : ℝ}
    (hf : f =ᵐ[ν] f') (hr : r =ᵐ[ν] r') (hm : m =ᵐ[ν] m')
    (h : Integrable f' ν ∧ (∫ x, f' x ∂ν) ≤
      K * (a * (∫ x, r' x ∂ν) + b * ∫ x, m' x ∂ν)) :
    Integrable f ν ∧ (∫ x, f x ∂ν) ≤ K * (a * (∫ x, r x ∂ν) + b * ∫ x, m x ∂ν) := by
  refine ⟨h.1.congr hf.symm, ?_⟩
  exact (integral_congr_ae hf).le.trans
    (h.2.trans_eq (congrArg₂ (fun R M : ℝ => K * (a * R + b * M))
      (integral_congr_ae hr).symm (integral_congr_ae hm).symm))

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

theorem reference_inclusion_ae (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    inclusion (Fin N × Fin 3) (fun _ => 0) u =ᵐ[volume] fun X : Configuration N =>
      radiationGraphInclusion (radiationSource (Fin N × Fin 3) (fun _ => 0) u X) :=
  (Filter.EventuallyEq.of_eq (congrArg (fun v : WaveSpace (Fin N × Fin 3) => ⇑v)
    (radiation_matches (Fin N × Fin 3) (fun _ => 0) u).symm)).trans
      (radiationGraphInclusion.coeFn_compLpL (radiationSource (Fin N × Fin 3) (fun _ => 0) u))

theorem reference_radiation_ae (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    radiation (Fin N × Fin 3) (fun _ => 0) u =ᵐ[volume] fun X : Configuration N =>
      radiationGraphDerivative (radiationSource (Fin N × Fin 3) (fun _ => 0) u X) := by
  unfold radiation
  exact radiationGraphDerivative.coeFn_compLpL (radiationSource (Fin N × Fin 3) (fun _ => 0) u)

/-- The source estimate for actual finite-spin L2 wave functions. -/
theorem source_bound (u : PauliReference.Ref N)
    (w massWeight radiationWeight : Configuration N → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw : ∀ᵐ X ∂volume, 0 ≤ w X) (hwm : AEStronglyMeasurable w volume)
    (hwr : ∀ᵐ X ∂volume, w X ≤ a * radiationWeight X)
    (hwM : ∀ᵐ X ∂volume, w X ≤ b * massWeight X)
    (hiM : Integrable (fun X : Configuration N => massWeight X * ∑ s : SpinIndex N,
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2))
    (hiR : Integrable (fun X : Configuration N => radiationWeight X * ∑ s : SpinIndex N,
      ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2)) :
    Integrable (fun X : Configuration N => w X * ∑ s : SpinIndex N, ‖PauliMagneticOperator.quantum (N := N) F χ hUV C e u s X‖ ^ 2) ∧
      (∫ X : Configuration N, w X * ∑ s : SpinIndex N, ‖PauliMagneticOperator.quantum (N := N) F χ hUV C e u s X‖ ^ 2) ≤
        PauliMagneticWeighted.constant (N := N) F χ hUV e *
          (a * (∫ X : Configuration N, radiationWeight X * ∑ s : SpinIndex N,
            ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2) +
           b * (∫ X : Configuration N, massWeight X * ∑ s : SpinIndex N,
            ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2)) := by
  let q : Configuration N → SpinIndex N → RadiationGraphSpace :=
    fun X s => radiationSource (Fin N × Fin 3) (fun _ => 0) (u s) X
  have hmass : (fun X : Configuration N => massWeight X * ∑ s : SpinIndex N,
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2) =ᵐ[volume]
      fun X : Configuration N => massWeight X * ∑ s : SpinIndex N, ‖radiationGraphInclusion (q X s)‖ ^ 2 := by
    exact weighted_square_sum_congr (X := Configuration N) (S := SpinIndex N)
      (H := PhotonFock) volume massWeight
      (fun s X => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
      (fun s X => radiationGraphInclusion (q X s))
      (fun s => reference_inclusion_ae (N := N) (u s))
  have hrad : (fun X : Configuration N => radiationWeight X * ∑ s : SpinIndex N,
      ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2) =ᵐ[volume]
      fun X : Configuration N => radiationWeight X * ∑ s : SpinIndex N, ‖radiationGraphDerivative (q X s)‖ ^ 2 := by
    exact weighted_square_sum_congr (X := Configuration N) (S := SpinIndex N)
      (H := PhotonFock) volume radiationWeight
      (fun s X => radiation (Fin N × Fin 3) (fun _ => 0) (u s) X)
      (fun s X => radiationGraphDerivative (q X s))
      (fun s => reference_radiation_ae (N := N) (u s))
  have hrep : (fun X : Configuration N => w X * ∑ s : SpinIndex N,
      ‖PauliMagneticOperator.quantum (N := N) F χ hUV C e u s X‖ ^ 2) =ᵐ[volume]
      fun X : Configuration N => w X * ∑ s : SpinIndex N,
        ‖PauliMagneticSpin.quantum (N := N) F χ hUV C e (fun n => particle X n) (q X) s‖ ^ 2 := by
    exact weighted_square_sum_congr (X := Configuration N) (S := SpinIndex N)
      (H := PhotonFock) volume w
      (fun s X => PauliMagneticOperator.quantum (N := N) F χ hUV C e u s X)
      (fun s X => PauliMagneticSpin.quantum (N := N) F χ hUV C e
        (fun n => particle X n) (q X) s)
      (PauliMagneticOperator.quantum_ae (N := N) F χ hUV C e u)
  have hm : AEStronglyMeasurable (fun X : Configuration N => w X * ∑ s : SpinIndex N,
      ‖PauliMagneticOperator.quantum (N := N) F χ hUV C e u s X‖ ^ 2) volume :=
    hwm.mul (Finset.univ.aestronglyMeasurable_fun_sum fun s _ =>
      (Lp.aestronglyMeasurable (PauliMagneticOperator.quantum (N := N) F χ hUV C e u s)).norm.pow 2)
  have h := PauliMagneticWeighted.source_bound (N := N) (X := Configuration N) (ν := volume)
    F χ hUV C e (fun X n => particle X n) q
    w massWeight radiationWeight ha hb hw hwr hwM (hm.congr hrep)
    (hiM.congr hmass) (hiR.congr hrad)
  exact transfer_bound volume hrep hrad hmass h


end PfHk.PauliMagneticPhysicalWeighted

