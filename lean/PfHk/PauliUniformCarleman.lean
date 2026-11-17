import PfHk.PauliOperatorCarlemanMass
import PfHk.PauliUCPSource
import PfHk.PhysicalCutoffGeometry
import PfHk.ExceptionalConfigurationGeometry

/-! Uniform cutoff Carleman estimates on the regular configuration
region. All physical estimates, local source identities and coefficient
radii are derived from the checked Pauli theorem. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PauliOperatorCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PauliLocalEnergy
  PfHk.PhysicalCommonFormDomain PfHk.CenteredPhysicalReference
  PfHk.PhysicalCutoffCommutator PfHk.SmoothCutoffBounds
  PfHk.PhysicalFieldRegularity PfHk.PhysicalLocalEnergy
  PfHk.PhysicalCarlemanInput PfHk.ExceptionalConfigurationGeometry

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

attribute [local instance] PhysicalLocalExternalCarleman.endpointPhotonRealInner
attribute [local irreducible] referenceSubspace inclusion

private theorem subradius {X : Type*} [MetricSpace X] {U : Set X}
    (hU : IsOpen U) {O : X} (hO : O ∈ U) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∃ R : ℝ, 0 < R ∧ R ≤ r ∧ R ≤ s ∧ Metric.ball O (4 * R) ⊆ U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU O hO
  let R := min r (min s (δ / 4))
  have hR : 0 < R := lt_min hr (lt_min hs (by positivity))
  have hRδ : R ≤ δ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨R, hR, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (Metric.ball_subset_ball (by linarith only [hRδ])).trans hball⟩

variable {N : ℕ}
variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

/-- The physical Pauli Carleman estimate supplies the uniform input to
continuation, including regularity away from a one-body exceptional set. -/
theorem uniform_localCarleman
    (B : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e)
    {Ω : Set PhysicalSourceCoordinates.Position}
    (a : PauliPhysicalLocalRegularity.RegularityOn A v Ω)
    (hΩ : IsOpen Ω) (hN : 0 < N)
    (α : ℝ) (hα : 0 < α) (E : ℝ) :
    UniformLocalCarleman F χ C e A v c hc E α (configurationDomain Ω N) := by
  intro O hO
  have hU := configurationDomain_isOpen hΩ N
  have hd : 0 < Fintype.card (Fin N × Fin 3) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hexρ := a.exists_physicalRegularity hΩ hO.2 hO.1 c
  let ρ := Classical.choose hexρ
  have hρ := (Classical.choose_spec hexρ).1
  let areg := Classical.choice (Classical.choose_spec hexρ).2
  let coeff := PauliLocalDomain.PhysicalRegularity.data A v c O ρ areg
  have hex := PauliPhysicalCarleman.physical_exists_uniform_estimate
    F χ C e A v c hc B.spectral B.coordinateSobolev B.joint B.friedrichs B.katoRellich
    B.domain B.graphNorm B.selfAdjoint areg hρ B.ultraviolet B.weyl B.weylGraph
    B.polar B.sphereGradient B.charts B.logPolar hd B.coreDensity B.annularCore
    α hα E
  let rB := Classical.choose hex
  have h₁ := Classical.choose_spec hex
  let τ₀ := Classical.choose h₁
  have h₂ := Classical.choose_spec h₁
  let C₂ := Classical.choose h₂
  have h₃ := Classical.choose_spec h₂
  let C₂e := Classical.choose h₃
  have h₄ := Classical.choose_spec h₃
  let families := Classical.choose h₄
  have hbase := Classical.choose_spec h₄
  have hexR := subradius hU hO hbase.1 (by positivity : 0 < ρ / 64)
  let R₀ := Classical.choose hexR
  have hR₀ := Classical.choose_spec hexR
  refine ⟨R₀, τ₀, 2080, hR₀.1, (hR₀.2.1.trans_lt hbase.2.2.2.1).le,
    hbase.2.2.2.2.1, by norm_num, hR₀.2.2.2, ?_⟩
  intro y hy R hR hRR₀ u heigen family ε hε hεR τ hτ
  let η := twiceSub (family.cutoff (R / 2)) (family.cutoff ε)
  let f := PauliLocalCutoffRules.commutator C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
    (vector A) (positive v c) (negative v c) η u (physicalDomain A v c hc u)
  have hyρ : y ∈ Metric.ball O (ρ / 64) := Metric.ball_subset_ball hR₀.2.2.1 hy
  have hRρ : R ≤ ρ / 64 := hRR₀.trans hR₀.2.2.1
  have hp := PauliUCPSource.annular_local_operatorPair coeff hρ C F χ e
    B.coordinateSobolev B.spectral B.joint B.friedrichs B.ultraviolet B.weyl B.weylGraph
    B.coreDensity hyρ hR hRρ hε hεR family E u (physicalDomain A v c hc u) heigen
  have hsupp (s : SpinIndex N) := buffered_annular_support (fun _ => 0) (u s)
    hR hε hεR (family.cutoff (R / 2)) (family.cutoff ε)
    (family.weight (R / 2) (half_pos hR)) (family.weight ε hε)
  have hyB : y ∈ Metric.ball O rB := Metric.ball_subset_ball hR₀.2.1 hy
  have hRB : R ≤ rB := hRR₀.trans hR₀.2.1
  have he := hbase.2.2.2.2.2.2.2 y hyB R hR hRB τ hτ
    (localize η.scalar u) f hp hsupp
  have hτ0 : 0 ≤ τ := zero_le_one.trans (hbase.2.2.2.2.1.trans hτ)
  have hRone : R < 1 := (hRB.trans_lt hbase.2.2.2.1).trans
    (by simpa only [Real.exp_zero] using
      (Real.exp_lt_exp.mpr (by norm_num : (-2 : ℝ) < 0)))
  exact mass_lintegral_of_estimate F χ C e A v c hc B.spectral he hτ0 hα hRone hsupp

end PfHk.PauliOperatorCarleman
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
