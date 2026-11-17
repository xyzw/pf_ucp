import PfHk.CenteredRadialGaugeEnergy
import GptLean.WeylRadiationOperator

/-! The actual centered gauge preserves the radiation operator domain.
Its frequency-weighted label is constructed as a Bochner integral of the
physical frequency-weighted kernels. The only extra physical moment is
the same `CarlemanUV` used throughout the radial gauge construction. -/

noncomputable section
namespace PfHk.CenteredRadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  GptLean.PhysicalNonattainmentFluxKernel PfHk.PhysicalFieldRegularity
  Gaussian
open PfHk.RadialGauge (energyComponent energyKernel)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N)

def omegaRay (θ : Configuration N) (r : ℝ) : WeightedPhotonKernel :=
  ∑ j : Fin N × Fin 3, θ j • ((-e) • omegaKernel F χ hUV j.2 (particle (O + r • θ) j.1))

theorem omegaRay_continuous (θ : Configuration N) : Continuous (omegaRay F χ hUV e O θ) := by
  apply continuous_finsetSum
  intro j _
  exact (continuous_const : Continuous (fun _ : ℝ => θ j)).smul
    ((continuous_const : Continuous (fun _ : ℝ => (-e : ℝ))).smul
      ((omegaKernel_continuous F χ hUV j.2).comp
        ((particleLinear j.1).continuous_of_finiteDimensional.comp
          (continuous_const.add (continuous_id.smul continuous_const)))))

def omegaLabel (X : Configuration N) : WeightedPhotonKernel :=
  ∫ s in (0 : ℝ)..1, omegaRay F χ hUV e O X s

theorem energyComponent_true_apply (q : RadialGauge.EnergyLabel) :
    energyComponent true q = q.val.2 := rfl

theorem component_true_apply (q : WeightedPhotonKernel) : component true q = q.val.2 := rfl

theorem energyComponent_mk (u v : Lp ℂ 2 photonMeasure)
    (hv : (u, v) ∈ PhysicalMultiplicationGraph.graph photonMeasure (H := ℂ)
      (fun p => (Real.sqrt ‖p.1‖ : ℂ))) :
    energyComponent true ⟨(u, v), hv⟩ = v := rfl

theorem energyKernel_snd (j : Fin 3) (X : FieldSpace) :
    energyComponent true (energyKernel F χ hUV j X) = component true (omegaKernel F χ hUV j X) := by
  exact (energyComponent_mk (physicalKernel F χ j X).val.1 (omegaKernel F χ hUV j X).val.2
    (RadialGauge.omegaKernel_sqrt_relation F χ hUV j X)).trans
      (component_true_apply (omegaKernel F χ hUV j X)).symm

theorem omegaRay_snd (θ : Configuration N) (r : ℝ) :
    component true (omegaRay F χ hUV e O θ r) =
      energyComponent true (energyRay F χ hUV e O θ r) := by
  simp only [omegaRay, energyRay, map_sum, map_smul, energyKernel_snd]

theorem omegaLabel_snd (X : Configuration N) :
    (omegaLabel F χ hUV e O X).val.2 = sqrtLabel F χ hUV e O X := by
  change component true (omegaLabel F χ hUV e O X) =
    energyComponent true (energyLabel F χ hUV e O X)
  rw [omegaLabel, energyLabel,
    ← (component true).intervalIntegral_comp_comm
      ((omegaRay_continuous F χ hUV e O X).intervalIntegrable 0 1),
    ← (energyComponent true).intervalIntegral_comp_comm
      ((energyRay_continuous F χ hUV e O X).intervalIntegrable 0 1)]
  exact intervalIntegral.integral_congr fun s _ => omegaRay_snd F χ hUV e O X s

theorem imaginary_omegaLabel_relation (X : Configuration N) :
    ∀ᵐ p ∂photonMeasure, (Complex.I • omegaLabel F χ hUV e O X).val.2 p =
      (Real.sqrt ‖p.1‖ : ℂ) * (Complex.I • (label F χ e O X).val.1) p := by
  have hcomp : (Complex.I • omegaLabel F χ hUV e O X).val.2 =
      Complex.I • sqrtLabel F χ hUV e O X := by
    change Complex.I • (omegaLabel F χ hUV e O X).val.2 = _
    rw [omegaLabel_snd]
  rw [hcomp]
  filter_upwards [sqrtLabel_relation F χ hUV e O X,
    Lp.coeFn_smul Complex.I (sqrtLabel F χ hUV e O X),
    Lp.coeFn_smul Complex.I (label F χ e O X).val.1] with p hp hs hl
  rw [hs, hl]
  simp only [Pi.smul_apply, smul_eq_mul, hp]
  ring

include hUV in
/-- The actual full radiation operator domain is unchanged by the gauge. -/
theorem unitary_radiationDomain_iff (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (X : Configuration N) (u : PhotonFock) :
    unitary F χ e O W X u ∈ radiationHamiltonian.domain ↔ u ∈ radiationHamiltonian.domain :=
  radiationHamiltonian_weyl_domain_iff C W (Complex.I • (label F χ e O X).val.1)
    (Complex.I • omegaLabel F χ hUV e O X) (imaginary_omegaLabel_relation F χ hUV e O X) u

/-- The operator graph transport is the existing Weyl radiation theorem
instantiated with the constructed physical frequency label. -/
theorem unitary_radiation_graph (C : CanonicalSectorCCR photonMeasure)
    (W : ConcreteWeylLaw photonMeasure) (X : Configuration N)
    (q : RadiationGraphSpace) (v : PhotonFock)
    (hv : (radiationGraphInclusion q, v) ∈ radiationHamiltonian.graph) :
    (unitary F χ e O W X (radiationGraphInclusion q),
      unitary F χ e O W X (v + kernelField C (Complex.I • omegaLabel F χ hUV e O X) q +
        (‖(Complex.I • omegaLabel F χ hUV e O X).val.2‖ ^ 2 : ℂ) • radiationGraphInclusion q)) ∈
      radiationHamiltonian.graph :=
  radiationHamiltonian_weyl_graph C W (Complex.I • (label F χ e O X).val.1)
    (Complex.I • omegaLabel F χ hUV e O X) (imaginary_omegaLabel_relation F χ hUV e O X) q v hv

end PfHk.CenteredRadialGauge
