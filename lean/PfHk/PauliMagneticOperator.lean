import PfHk.PauliMagneticSpin
import PfHk.PauliReference

/-! The quantum Zeeman multiplication as an actual L2 vector. Its pointwise
representative is the physical Pauli contraction of the curl field. -/

noncomputable section
namespace PfHk.PauliMagneticOperator

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.PhysicalNonattainmentFluxKernel Gaussian
  GptLean.SymmetricLift GptLean.Representability
  PfHk.PhysicalFieldRegularity PfHk.PauliSpin

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

attribute [local irreducible] radiationSource inclusion radiation
  RadialGauge.momentBound PauliMagneticField.field

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
  (C : CanonicalSectorCCR photonMeasure)

def profile (n : Fin N) (μ : Fin 3) (X : Configuration N) : WeightedPhotonKernel :=
  PauliMagneticField.kernel F χ hUV μ (particle X n)

theorem profile_measurable (n : Fin N) (μ : Fin 3) :
    AEStronglyMeasurable (profile F χ hUV n μ) volume :=
  ((PauliMagneticField.kernel_continuous F χ hUV μ).comp
    (particleLinear n).continuous_of_finiteDimensional).aestronglyMeasurable

theorem profile_bound (n : Fin N) (μ : Fin 3) :
    ∀ᵐ X ∂volume, ‖profile F χ hUV n μ X‖ ≤ 2 * RadialGauge.momentBound F χ hUV :=
  ae_of_all _ fun X => PauliMagneticField.kernel_norm_le F χ hUV μ (particle X n)

def component (n : Fin N) (μ : Fin 3)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) : WaveSpace (Fin N × Fin 3) :=
  spatialField volume C (profile F χ hUV n μ) (profile_measurable F χ hUV n μ)
    (2 * RadialGauge.momentBound F χ hUV) (profile_bound F χ hUV n μ)
    (radiationSource (Fin N × Fin 3) (fun _ => 0) u)

theorem component_ae (n : Fin N) (μ : Fin 3)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    component F χ hUV C n μ u =ᵐ[volume] fun X =>
      PauliMagneticField.field F χ hUV C μ (particle X n)
        (radiationSource (Fin N × Fin 3) (fun _ => 0) u X) := by
  unfold component PauliMagneticField.field
  exact spatialField_ae volume C (profile F χ hUV n μ) (profile_measurable F χ hUV n μ)
    (2 * RadialGauge.momentBound F χ hUV) (profile_bound F χ hUV n μ)
    (radiationSource (Fin N × Fin 3) (fun _ => 0) u)

theorem sigma_ae {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ν : Measure X)
    (n : Fin N) (μ : Fin 3) (u : SpinIndex N → Lp H 2 ν) (s : SpinIndex N) :
    (fun x => sigmaFamily n μ u s x) =ᵐ[ν] fun x => sigmaFamily n μ (fun t => u t x) s := by
  simp only [sigmaFamily]
  split_ifs
  · exact Filter.EventuallyEq.rfl
  · exact Lp.coeFn_smul _ _
  · exact Lp.coeFn_smul _ _

theorem sum_sigma_ae {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ν : Measure X)
    (n : Fin N) (u : Fin 3 → SpinIndex N → Lp H 2 ν)
    (f : Fin 3 → SpinIndex N → X → H)
    (hu : ∀ μ t, (fun x => u μ t x) =ᵐ[ν] f μ t) (s : SpinIndex N) :
    (fun x => (∑ μ : Fin 3, sigmaFamily n μ (u μ) s : Lp H 2 ν) x) =ᵐ[ν]
      fun x => ∑ μ : Fin 3, sigmaFamily n μ (fun t => f μ t x) s := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun μ : Fin 3 => sigmaFamily n μ (u μ) s),
    ae_all_iff.mpr (fun μ => sigma_ae ν n μ (u μ) s),
    ae_all_iff.mpr (fun μ => ae_all_iff.mpr (hu μ))] with x hx hσ hf
  calc
    _ = ∑ μ : Fin 3, sigmaFamily n μ (u μ) s x := by
      simpa only [Finset.sum_apply] using hx
    _ = _ := Finset.sum_congr rfl (fun μ _ => (hσ μ).trans
      (congrArg (fun v => sigmaFamily n μ v s) (funext (hf μ))))

theorem smul_sum_ae {J X H : Type*} [Fintype J] [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (ν : Measure X)
    (c : ℂ) (u : J → Lp H 2 ν) (f : J → X → H)
    (hu : ∀ j, (fun x => u j x) =ᵐ[ν] f j) :
    (fun x => (c • ∑ j, u j : Lp H 2 ν) x) =ᵐ[ν] fun x => c • ∑ j, f j x := by
  filter_upwards [Lp.coeFn_smul c (∑ j, u j), Lp.coeFn_finsetSum Finset.univ u,
    ae_all_iff.mpr hu] with x hx hs hf
  simpa only [Pi.smul_apply, Finset.sum_apply, hf] using
    hx.trans (congrArg (fun v => c • v) hs)

def contraction (n : Fin N) (u : PauliReference.Ref N) (s : SpinIndex N) :
    WaveSpace (Fin N × Fin 3) :=
  ∑ μ : Fin 3, sigmaFamily n μ (fun t => component F χ hUV C n μ (u t)) s

theorem contraction_ae (n : Fin N) (u : PauliReference.Ref N) (s : SpinIndex N) :
    contraction F χ hUV C n u s =ᵐ[volume] fun X =>
      PauliMagneticSpin.contraction F χ hUV C n (particle X n)
        (fun t => radiationSource (Fin N × Fin 3) (fun _ => 0) (u t) X) s := by
  unfold contraction PauliMagneticSpin.contraction
  exact sum_sigma_ae volume n
    (fun μ t => component F χ hUV C n μ (u t))
    (fun μ t X => PauliMagneticField.field F χ hUV C μ (particle X n)
      (radiationSource (Fin N × Fin 3) (fun _ => 0) (u t) X))
    (fun μ t => component_ae F χ hUV C n μ (u t)) s

def quantum (e : ℝ) (u : PauliReference.Ref N) (s : SpinIndex N) :
    WaveSpace (Fin N × Fin 3) :=
  ((-e / 2 : ℝ) : ℂ) • ∑ n, contraction F χ hUV C n u s

theorem quantum_ae (e : ℝ) (u : PauliReference.Ref N) (s : SpinIndex N) :
    quantum F χ hUV C e u s =ᵐ[volume] fun X =>
      PauliMagneticSpin.quantum F χ hUV C e (fun n => particle X n)
        (fun t => radiationSource (Fin N × Fin 3) (fun _ => 0) (u t) X) s := by
  unfold quantum PauliMagneticSpin.quantum
  exact smul_sum_ae volume ((-e / 2 : ℝ) : ℂ)
    (fun n => contraction F χ hUV C n u s)
    (fun n X => PauliMagneticSpin.contraction F χ hUV C n (particle X n)
      (fun t => radiationSource (Fin N × Fin 3) (fun _ => 0) (u t) X) s)
    (fun n => contraction_ae F χ hUV C n u s)

end PfHk.PauliMagneticOperator
