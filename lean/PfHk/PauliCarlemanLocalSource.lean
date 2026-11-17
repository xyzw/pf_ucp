import PfHk.PauliCarlemanOperatorSource
import PfHk.PauliLocalOperatorDomain

/-! A local Pauli weak source yields local orbital component sources
after subtracting the actual two Zeeman terms. A fixed exterior cutoff
on the original source equals one on each target Carleman ball. -/

noncomputable section
namespace PfHk.PauliCarlemanLocalSource

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.PauliGroundState PfHk.PauliSpin PfHk.PhysicalLocalEnergy
  PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain PfHk.CenteredPhysicalReference
  PfHk.WeylGraphC1Calculus PfHk.WeylCoreReference
  PfHk.FriedrichsDivergenceBackground PfHk.SmoothCutoffBounds
  PfHk.KatoRellichBackground PfHk.PhysicalCoefficientLocality PfHk.PauliLocalDomain

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] referenceSubspace inclusion externalForm
  PauliMagneticClassicalOperator.zeeman PauliMagneticOperator.quantum

/-- A common small radius keeps nearby target balls in the fixed
interior ball used by the local operator-domain argument. -/
theorem target_ball_subset_inner {X : Type*} [PseudoMetricSpace X]
    {O₀ O : X} {r R ρ : ℝ} (hO : O ∈ Metric.ball O₀ r)
    (hR : R ≤ r) (hr : r ≤ ρ / 16) :
    Metric.ball O R ⊆ Metric.ball O₀ (ρ / 8) := by
  intro x hx
  have ht := dist_triangle x O O₀
  have ho : dist O O₀ < r := hO
  have hx' : dist x O < R := hx
  change dist x O₀ < ρ / 8
  linarith only [ht, ho, hx', hR, hr]

private theorem linear_shift {H : Type*} [AddCommGroup H] [Module ℂ H]
    (T : H →ₗ[ℂ] H) (f u : H) (E : ℂ) (hu : T u = u) :
    T (f + E • u) = T f + E • u := by
  rw [map_add, map_smul, hu]

variable {N : ℕ} {O : Configuration N} {ρ : ℝ}
  (a : Data O ρ) (hρ : 0 < ρ)
  (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff) (e : ℝ)
  (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)
  (friedrichs : StandardFriedrichsDivergence)
  (hUV : CarlemanUV χ) (W : ConcreteWeylLaw photonMeasure)
  (G : StandardWeylGraphC1 W) (D : StandardWeylFormCoreDensity W G)
  (KR : StandardKatoRellich)
  (hD : HaslerHerbstDomain C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hG : HaslerHerbstGraphNorm C (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e)
  (hSA : SelfAdjointGraph (PhysicalExternalOperator.freeHilbertGraph (fun _ => 0) C
    (profile (N := N) F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e))

include hρ S spectral joint friedrichs W G D KR hD hG hSA in
/-- The magnetic multipliers, comparison domains and orbital weak
equations follow from the actual local Pauli weak equation. -/
theorem orbital_pairs (family : BufferedFamily O)
    (u : Ref N) (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
    (hs : ∀ s, ∀ᵐ X ∂volume, X ∉ Metric.ball O (ρ / 8) →
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X = 0)
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hf : PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e
      a.orbital.vector a.orbital.positive a.orbital.negative (Metric.ball O (ρ / 2)) u hu f) :
    ∃ hB : ∀ n k s, HasMultiplier
        (CoordinateSobolev.coordinateCoefficient n (a.truncatedMagnetic n k))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)),
      (∀ s, ComparisonDomain (fun _ => 0) (u s)) ∧
      ∀ s, PhysicalCutoffCommutator.IsLocalOperatorPair (fun _ => 0) C
        (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
        e a.orbital.vector a.orbital.positive a.orbital.negative
        (Metric.ball O (ρ / 2)) (u s) (hu s)
        ((family.cutoff (ρ / 8)).scalar.multiplier (f s) -
          PauliMagneticClassicalOperator.zeeman a.truncatedMagnetic u hB s -
          PauliMagneticOperator.quantum F χ hUV C e u s) := by
  have hpair := truncated_operatorPair a hρ C F χ e S spectral joint friedrichs
    hUV W G D family u hu hs f hf
  have hex := PauliCarlemanOperatorSource.orbital_pairs (a.orbital.truncated hρ) C
    (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
    e F χ hUV a.truncatedMagnetic S spectral joint hD a.exponent_gt_two
    a.truncatedMagnetic_memLp friedrichs KR hG hSA u (truncatedDomain a hρ u hu hs)
    (fun s => (family.cutoff (ρ / 8)).scalar.multiplier (f s)) hpair
  let hB := Classical.choose hex
  have hcomp := (Classical.choose_spec hex).1
  have horb := (Classical.choose_spec hex).2
  refine ⟨hB, hcomp, ?_⟩
  intro s z hz hzs
  have hZ := a.orbital.agreement hρ
    (inclusion (Fin N × Fin 3) (fun _ => 0) z) hzs
  have hz' := domain_congr (fun _ => 0) a.orbital.vector (a.orbital.truncated hρ).vector
    a.orbital.positive a.orbital.negative (a.orbital.truncated hρ).positive
    (a.orbital.truncated hρ).negative z hz hZ
  have heq := PhysicalCoefficientLocality.form_congr (fun _ => 0)
    a.orbital.vector (a.orbital.truncated hρ).vector a.orbital.positive a.orbital.negative
    (a.orbital.truncated hρ).positive (a.orbital.truncated hρ).negative C
    (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e
    z (u s) hz (hu s) hz' (truncatedDomain a hρ u hu hs s) hZ
    (supported_agreement a hρ u hs s)
  exact heq.trans (horb s z hz')

include hρ S spectral joint friedrichs W G D KR hD hG hSA in
/-- The shifted local source uses the same form domain and coefficient
data. The energy is moved into a bounded mass perturbation. -/
theorem orbital_pairs_shifted (family : BufferedFamily O)
    (u : Ref N) (hu : Domain a.orbital.vector a.orbital.positive a.orbital.negative u)
    (hs : ∀ s, ∀ᵐ X ∂volume, X ∉ Metric.ball O (ρ / 8) →
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X = 0)
    (E : ℝ) (f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hf : PauliLocalOperatorTransfer.IsLocalOperatorPair C F χ e
      a.orbital.vector a.orbital.positive a.orbital.negative (Metric.ball O (ρ / 2)) u hu
      (fun s => f s + (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s))) :
    ∃ hB : ∀ n k s, HasMultiplier
        (CoordinateSobolev.coordinateCoefficient n (a.truncatedMagnetic n k))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)),
      (∀ s, ComparisonDomain (fun _ => 0) (u s)) ∧
      ∀ s, PhysicalCutoffCommutator.IsLocalOperatorPair (fun _ => 0) C
        (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
        e a.orbital.vector a.orbital.positive a.orbital.negative
        (Metric.ball O (ρ / 2)) (u s) (hu s)
        ((family.cutoff (ρ / 8)).scalar.multiplier (f s) +
          (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s) -
          PauliMagneticClassicalOperator.zeeman a.truncatedMagnetic u hB s -
          PauliMagneticOperator.quantum F χ hUV C e u s) := by
  have hex := orbital_pairs a hρ C F χ e S spectral joint friedrichs hUV W G D
    KR hD hG hSA family u hu hs
    (fun s => f s + (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) hf
  let hB := Classical.choose hex
  have hcomp := (Classical.choose_spec hex).1
  have horb := (Classical.choose_spec hex).2
  refine ⟨hB, hcomp, ?_⟩
  intro s
  have ht : 0 < ρ / 8 := div_pos hρ (by norm_num)
  have hfix := (BufferedCutoffLocality.cutoff_action family ht
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hs s)).1
  have hshift := linear_shift ((family.cutoff (ρ / 8)).scalar.multiplier.toLinearMap)
    (f s) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (E : ℂ) hfix
  have heq := congrArg (fun z : WaveSpace (Fin N × Fin 3) =>
    z - PauliMagneticClassicalOperator.zeeman a.truncatedMagnetic u hB s -
      PauliMagneticOperator.quantum F χ hUV C e u s) hshift
  exact (congrArg (fun z : WaveSpace (Fin N × Fin 3) =>
    PhysicalCutoffCommutator.IsLocalOperatorPair (fun _ => 0) C
      (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
      e a.orbital.vector a.orbital.positive a.orbital.negative
      (Metric.ball O (ρ / 2)) (u s) (hu s) z) heq).mp (horb s)

theorem annular_supported_inner {O' : Configuration N} {r R : ℝ}
    (hO : O' ∈ Metric.ball O r) (hR : R ≤ r) (hr : r ≤ ρ / 16)
    (u : Ref N)
    (hs : ∀ s, PhysicalCarlemanInput.AnnularSupport
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O' R) :
    ∀ s, ∀ᵐ X ∂volume, X ∉ Metric.ball O (ρ / 8) →
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X = 0 := by
  intro s
  have hsupport := PhysicalExternalSource.annularSupport_supported_ball _ (hs s)
  exact hsupport.mono fun X hX hnot => hX (fun hx => hnot (target_ball_subset_inner hO hR hr hx))

include hρ in
theorem cutoff_one_on_target (family : BufferedFamily O)
    {O' : Configuration N} {r R : ℝ}
    (hO : O' ∈ Metric.ball O r) (hR : R ≤ r) (hr : r ≤ ρ / 16) :
    ∀ X ∈ Metric.ball O' R, (family.cutoff (ρ / 8)).scalar.weight X = 1 := by
  intro X hX
  have ht : 0 < ρ / 8 := div_pos hρ (by norm_num)
  have hsmall : dist X O < ρ / 8 := target_ball_subset_inner hO hR hr hX
  exact (congrArg (fun w : Configuration N → ℝ => w X) (family.weight (ρ / 8) ht)).trans
    (SmoothCutoffBounds.buffered_scaled_one ht (by
      change dist X O ≤ 5 * (ρ / 8) / 4
      linarith only [hsmall, ht]))

end PfHk.PauliCarlemanLocalSource

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
