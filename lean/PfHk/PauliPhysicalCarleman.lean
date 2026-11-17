import PfHk.PauliCarlemanEstimate
import PfHk.PauliCarlemanMagneticAbsorption
import PfHk.PauliCarlemanSourceIdentity
import PfHk.PauliCarlemanSmallness

/-! Uniform Carleman estimate for the actual local Pauli Hamiltonian,
including a fixed energy shift. The coefficient assumptions determine
the radius and parameter. Both Zeeman errors are absorbed using proved
physical bounds, with no smallness or comparison-domain premise. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliPhysicalCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput
  PfHk.PhysicalCutoffCommutator PfHk.PhysicalExternalOperator
  PfHk.KatoRellichBackground PfHk.FriedrichsDivergenceBackground
  PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs PfHk.PauliSpin
  PfHk.WeylGraphC1Calculus PfHk.PolarCalculus PfHk.SphereCoreGeometry
  PfHk.OrdinaryPolarSobolevChart

attribute [local instance] PhysicalLocalExternalCarleman.endpointPhotonRealInner

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

private theorem radius_lt_one {r : ℝ} (h : r < Real.exp (-2)) : r < 1 :=
  h.trans (by simpa only [Real.exp_zero] using
    (Real.exp_lt_exp.mpr (by norm_num : (-2 : ℝ) < 0)))

variable {N : ℕ} {O₀ : Configuration N} {ρ : ℝ}
attribute [local irreducible] referenceSubspace inclusion
  PauliCarlemanClassical.coefficient PauliCarlemanQuantumShift.radiationCoefficient
  PauliCarlemanQuantumShift.massCoefficient PauliMagneticOperator.quantum

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (a : PauliLocalDomain.Data O₀ ρ)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (S : CoordinateSobolev.Data PhotonFock N)
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence) (KR : StandardKatoRellich)
  (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hSA : SelfAdjointGraph (freeHilbertGraph (fun _ => 0) C (profile (N := N) F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e))

include S joint friedrichs KR hD hG hSA

/-- The physical Pauli Carleman and spin-summed mixed estimates hold on
one radius and for all larger parameters, uniformly in nearby centers
and smaller balls. The source relation is H_P u = f + E u. -/
theorem exists_uniform_estimate (hρ : 0 < ρ) (hUV : CarlemanUV χ)
    (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
    (charts : StandardPolarSobolevCharts N) (L : StandardLogPolarCalculus (Fin N × Fin 3))
    (hN : 0 < Fintype.card (Fin N × Fin 3))
    (coreDensity : WeylCoreReference.StandardWeylFormCoreDensity W B)
    (core : ∀ O : Configuration N, AnnularCoreApproximation C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e)
    (α : ℝ) (hα : 0 < α) (E : ℝ) :
    ∃ r₀ τ₀ C₂ C₂e : ℝ, ∃ family : ∀ O : Configuration N, BufferedFamily O,
      0 < r₀ ∧ r₀ ≤ ρ / 16 ∧ 2 * r₀ ≤ Real.exp (-2) ∧ r₀ < Real.exp (-2) ∧
      1 ≤ τ₀ ∧ 0 ≤ C₂ ∧ 0 ≤ C₂e ∧
      ∀ O ∈ Metric.ball O₀ r₀, ∀ (R : ℝ) (hR : 0 < R), R ≤ r₀ →
      ∀ τ : ℝ, τ₀ ≤ τ →
      ∀ (u : PauliReference.Ref N)
        (hu : PauliGroundState.Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
        (f : SpinIndex N → WaveSpace (Fin N × Fin 3)),
        PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e a.orbital.vector
          a.orbital.positive a.orbital.negative (Metric.ball O₀ (ρ / 2)) u hu
          (fun s => f s + (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) →
        (∀ s, AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R) →
        Estimate F χ C e a.orbital spectral (family O) R hR τ α C₂ C₂e u hu f := by
  have hOrb := PauliCarlemanFinite.exists_uniform_estimate (T := SpinIndex N)
    F χ C e a.orbital spectral S joint friedrichs KR hD hG hSA hρ hUV W B P G
    charts L hN coreDensity core α hα
  let rB := Classical.choose hOrb
  have h₁ := Classical.choose_spec hOrb
  let τB := Classical.choose h₁
  have h₂ := Classical.choose_spec h₁
  let C₂ := Classical.choose h₂
  have h₃ := Classical.choose_spec h₂
  let C₂e := Classical.choose h₃
  have h₄ := Classical.choose_spec h₃
  let family := Classical.choose h₄
  have hbase := Classical.choose_spec h₄
  let exponents : Fin 2 → ℝ := fun j => if j = 0 then 4 - 2 * (3 / a.exponent) else 4
  have hexponents (j : Fin 2) : 0 < exponents j := by
    change 0 < (if j = 0 then 4 - 2 * (3 / a.exponent) else 4)
    split_ifs
    · exact (CarlemanAlgebra.scalar_exponents a.exponent_gt_two).2
    · norm_num
  have hRadius := PauliCarlemanRadii.exists_common_radius α exponents hexponents hbase.1
  let r₀ := Classical.choose hRadius
  have hr := Classical.choose_spec hRadius
  have hrρ : r₀ ≤ ρ / 16 := hr.2.1.trans hbase.2.1
  have hrone : r₀ < 1 := radius_lt_one hr.2.2.2.1
  have hexp0 : exponents 0 = 4 - 2 * (3 / a.exponent) := ite_eq_left rfl
  have hexp1 : exponents 1 = 4 := ite_eq_right (by decide)
  have hmass (r : ℝ) (hrp : 0 < r) (hrr : r ≤ r₀) :
      r ^ (4 : ℝ) / CarlemanWeights.beta α (-Real.log r) ≤ 1 :=
    (congrArg (fun b : ℝ => r ^ b / CarlemanWeights.beta α (-Real.log r) ≤ 1) hexp1).mp
      (hr.2.2.2.2.1 1 r hrp hrr)
  let Acl := PauliCarlemanClassical.coefficient S a.truncatedMagnetic a.exponent 1
    (4 * 6144) (4 * C₂)
  let Arad := PauliCarlemanQuantumShift.radiationCoefficient (N := N) F χ e hUV r₀
  let Amass := PauliCarlemanQuantumShift.massCoefficient (N := N) F χ e hUV E 1
  have hParameter := PauliCarlemanSmallness.exists_parameter a.exponent_gt_two
    (by norm_num : (0 : ℝ) < 1 / 8) Acl Arad Amass
  let τM := Classical.choose hParameter
  have hτM := Classical.choose_spec hParameter
  let τ₀ := max τB τM
  refine ⟨r₀, τ₀, C₂, C₂e, family, hr.1, hrρ, hr.2.2.1, hr.2.2.2.1,
    hbase.2.2.2.1.trans (le_max_left _ _), hbase.2.2.2.2.1, hbase.2.2.2.2.2.1, ?_⟩
  intro O hO R hR hRr τ hτ u hu f hf hsupp
  have hOB : O ∈ Metric.ball O₀ rB := (Metric.mem_ball.mp hO).trans_le hr.2.1
  have hRB : R ≤ rB := hRr.trans hr.2.1
  have hτB : τB ≤ τ := (le_max_left τB τM).trans hτ
  have hτ0 : 0 < τ := (by norm_num : (0 : ℝ) < 1).trans_le
    (hbase.2.2.2.1.trans hτB)
  have h2R : 2 * R ≤ Real.exp (-2) :=
    (mul_le_mul_of_nonneg_left hRr (by norm_num)).trans hr.2.2.1
  have hsInner := PauliCarlemanLocalSource.annular_supported_inner hO hRr hrρ u hsupp
  have hpairs := PauliCarlemanLocalSource.orbital_pairs_shifted a hρ C F χ e S spectral joint
    friedrichs hUV W B coreDensity KR hD hG hSA (family O₀) u hu hsInner E f hf
  let hB := Classical.choose hpairs
  have hcomp := (Classical.choose_spec hpairs).1
  have hpair := (Classical.choose_spec hpairs).2
  let g := PauliCarlemanSourceIdentity.orbitalSource F χ C e hUV a.truncatedMagnetic
    (family O₀) ρ E u hB f
  have he := hbase.2.2.2.2.2.2 O hOB R hR hRB τ hτB u hu g hpair hsupp
  have hdyadic (j : ℕ) :
      radius R j ^ (4 - 2 * (3 / a.exponent)) / dyadicBeta α R j ≤ 1 :=
    (congrArg (fun b : ℝ => radius R j ^ b / dyadicBeta α R j ≤ 1) hexp0).mp
      (hr.2.2.2.2.2 0 R hR hRr j)
  have hop := PauliCarlemanSourceIdentity.orbitalSource_ae_on_target F χ C e hUV
    a.truncatedMagnetic (family O₀) ρ E u hB f hρ hO hRr hrρ
  have hsmall := (hτM.2 τ ((le_max_right τB τM).trans hτ)).le
  have habs := magnetic_source_absorption F χ C e a.orbital S spectral joint
    a.truncatedMagnetic a.exponent_gt_two a.truncatedMagnetic_memLp hUV E
    hτ0 hα h2R hRr hrone u hu hcomp hB g f hsupp he hmass hdyadic hop hsmall
  exact of_orbital F χ C e a.orbital spectral he
    hbase.2.2.2.2.1 hbase.2.2.2.2.2.1 habs.1 habs.2.2

end PfHk.PauliPhysicalCarleman

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
