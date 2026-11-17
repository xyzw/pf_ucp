import PfHk.PauliMagneticRelativeAlgebra
import PfHk.PauliMagneticClassicalOperator
import PfHk.PauliMagneticPhysicalWeighted
import PfHk.PhysicalExternalRelativeBound
import PfHk.PauliSquareForm

/-! Actual magnetic multipliers on the finite-spin comparison domain.
The relative estimates follow from the coordinate Sobolev and physical
radiation estimates. The classical form agrees with its L2 source only
where that source has been constructed. -/

noncomputable section
namespace PfHk.PauliMagneticRelative

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.CoordinateSobolev
  PfHk.PhysicalFieldRegularity PfHk.PauliSpin PfHk.InfinitesimalBound
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
attribute [local irreducible] inclusion ordinary radiation roughMultiply
  referenceSubspace PauliMagneticOperator.quantum
  PauliMagneticClassicalOperator.term FiniteFiberL2.bundle
  PauliMagneticClassicalOperator.zeeman




variable {N : ℕ}


theorem classical_pairing
    (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (z u : PauliReference.Ref N)
    (hB : ∀ n μ s, HasMultiplier (coordinateCoefficient n (B n μ))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))) :
    PauliSquareForm.classicalForm B z u =
      ∑ s, inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (PauliMagneticClassicalOperator.zeeman B u hB s) := by
  have hp (n : Fin N) (k : Fin 3) (s t : SpinIndex N) :
      PauliClassicalCurlForm.pairing n (B n k)
        (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u t)) =
      inner ℂ (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
        (PauliMagneticClassicalOperator.term B u hB n k t) :=
    scalar_pairing_eq_inner (H := PhotonFock) (ν := volume) (coordinateCoefficient n (B n k))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u t))
      (PauliMagneticClassicalOperator.term B u hB n k t)
      (PauliMagneticClassicalOperator.term_ae B u hB n k t)
  unfold PauliSquareForm.classicalForm PauliMagneticClassicalOperator.zeeman
  exact half_trace_pairing (H := WaveSpace (Fin N × Fin 3))
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
    (PauliMagneticClassicalOperator.term B u hB)
    (fun n k s t => PauliClassicalCurlForm.pairing n (B n k)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (z s))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u t))) hp


variable (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ)

/-- Unweighted L2 magnetic bound on the actual reference spinors. -/
theorem quantum_norm_sq (u : PauliReference.Ref N) :
    ‖FiniteFiberL2.bundle (PauliMagneticOperator.quantum F χ hUV C e u)‖ ^ 2 ≤
      PauliMagneticWeighted.constant (N := N) F χ hUV e *
        ((∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2) +
          ∑ s, ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2) := by
  exact unweighted_norm_bound (H := PhotonFock)
    (PauliMagneticOperator.quantum F χ hUV C e u)
    (fun s => radiation (Fin N × Fin 3) (fun _ => 0) (u s))
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    (PauliMagneticWeighted.constant (N := N) F χ hUV e)
    (PauliMagneticPhysicalWeighted.source_bound F χ hUV C e u
      (fun _ => 1) (fun _ => 1) (fun _ => 1) (a := 1) (b := 1)
      zero_le_one zero_le_one (ae_of_all _ fun _ => zero_le_one)
      aestronglyMeasurable_const (ae_of_all _ fun _ => by norm_num)
      (ae_of_all _ fun _ => by norm_num)
      (sum_norm_sq_integrable (H := PhotonFock) _) (sum_norm_sq_integrable (H := PhotonFock) _)).2





variable {X : Type*}

theorem classical_multipliers
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    {p : ℝ} (hp : 2 < p) (hBp : ∀ n μ, MemLp (B n μ) (ENNReal.ofReal p) volume)
    (u : PauliReference.Ref N)
    (hu : ∀ s, ∃ L : WaveSpace (Fin N × Fin 3), IsComparisonPair (fun _ => 0) (u s) L) :
    ∀ n μ s, HasMultiplier (coordinateCoefficient n (B n μ))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) := by
  intro n μ s
  exact Classical.choose (PhysicalCoordinateMultipliers.scalar_multiplier S spectral joint hp
    n (B n μ) (hBp n μ) (u s) (hu s))



private theorem classical_norm_le
    (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (u : PauliReference.Ref N)
    (hB : ∀ n μ s, HasMultiplier (coordinateCoefficient n (B n μ))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))) :
    ‖FiniteFiberL2.bundle (PauliMagneticClassicalOperator.zeeman B u hB)‖ ≤
      (1 / 2 : ℝ) * ∑ n, ∑ μ : Fin 3,
        ‖FiniteFiberL2.bundle (PauliMagneticClassicalOperator.term B u hB n μ)‖ := by
  unfold PauliMagneticClassicalOperator.zeeman
  exact scaled_sigma_bundle_norm_le (H := PhotonFock) (PauliMagneticClassicalOperator.term B u hB)

/-- Classical Zeeman multiplication is infinitesimally bounded on the
finite-spin comparison graph for every raw global Lp coefficient p > 2. -/
theorem classical_comparison_relative
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    {p : ℝ} (hp : 2 < p) (hBp : ∀ n μ, MemLp (B n μ) (ENNReal.ofReal p) volume)
    (u : X → PauliReference.Ref N) (L : X → SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hL : ∀ x s, IsComparisonPair (fun _ => 0) (u x s) (L x s))
    (hB : ∀ x n μ s, HasMultiplier (coordinateCoefficient n (B n μ))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u x s))) :
    Bound (fun x => ‖FiniteFiberL2.bundle (L x)‖) (fun x => ‖PauliReference.wave (u x)‖)
      (fun x => ‖FiniteFiberL2.bundle (PauliMagneticClassicalOperator.zeeman B (u x) (hB x))‖) := by
  have hp0 : 0 < p := by linarith
  have hs0 : 0 ≤ 3 / p := by positivity
  have hs2 : 3 / p < 2 := (div_lt_iff₀ hp0).mpr (by linarith)
  have ht (n : Fin N) (μ : Fin 3) (s : SpinIndex N) :
      Bound (fun x => ‖FiniteFiberL2.bundle (L x)‖) (fun x => ‖PauliReference.wave (u x)‖)
        (fun x => ‖PauliMagneticClassicalOperator.term B (u x) (hB x) n μ s‖) := by
    apply enlarge_relative (fun x => norm_coordinate_le_bundle (L x) s)
      (fun x => norm_coordinate_le_bundle
        (fun t => inclusion (Fin N × Fin 3) (fun _ => 0) (u x t)) s)
    apply PhysicalRelativeMultiplier.of_fractional_norm_sq spectral
      (fun x => u x s) (fun x => L x s) _ (fun x => hL x s) hs0 hs2
      (PhysicalCoordinateMultipliers.coefficientNormSq_nonneg S p (B n μ))
    intro x
    unfold PauliMagneticClassicalOperator.term
    exact Classical.choose_spec (PhysicalCoordinateMultipliers.scalar_multiplier S spectral joint hp
      n (B n μ) (hBp n μ) (u x s) ⟨L x s, hL x s⟩)
  have hb (n : Fin N) (μ : Fin 3) := bundle_relative
    (fun x => PauliMagneticClassicalOperator.term B (u x) (hB x) n μ)
    (fun x => norm_nonneg (FiniteFiberL2.bundle (L x))) (ht n μ)
  have hsum := InfinitesimalBound.sum Finset.univ
    (fun n x => ∑ μ : Fin 3,
      ‖FiniteFiberL2.bundle (PauliMagneticClassicalOperator.term B (u x) (hB x) n μ)‖)
    (fun x => norm_nonneg (FiniteFiberL2.bundle (L x)))
    (fun n _ => InfinitesimalBound.sum Finset.univ _
      (fun x => norm_nonneg (FiniteFiberL2.bundle (L x))) (fun μ _ => hb n μ))
  exact InfinitesimalBound.mono (scale_relative (1 / 2) (by norm_num) hsum
    (fun x => norm_nonneg (FiniteFiberL2.bundle (L x))))
    (fun x => classical_norm_le B (u x) (hB x))

/-- The comparison form controls the total radiation and mass energy. -/
theorem comparison_radiation_mass_le
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (u : PauliReference.Ref N) (L : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hL : ∀ s, IsComparisonPair (fun _ => 0) (u s) (L s)) :
    (∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2) +
      (∑ s, ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2) ≤
        ‖PauliReference.wave u‖ * ‖FiniteFiberL2.bundle L‖ :=
  radiation_mass_bound (H := PhotonFock)
    (fun s => radiation (Fin N × Fin 3) (fun _ => 0) (u s))
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) L
    (fun s i => ordinary (Fin N × Fin 3) (fun _ => 0) i (u s))
    (fun s => comparison_form_le_graph spectral (hL s))

/-- The quantum Zeeman source has arbitrarily small comparison-operator
relative bound, uniformly on the actual finite-spin domain. -/
theorem quantum_comparison_relative
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (u : X → PauliReference.Ref N) (L : X → SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hL : ∀ x s, IsComparisonPair (fun _ => 0) (u x s) (L x s)) :
    Bound (fun x => ‖FiniteFiberL2.bundle (L x)‖) (fun x => ‖PauliReference.wave (u x)‖)
      (fun x => ‖FiniteFiberL2.bundle (PauliMagneticOperator.quantum F χ hUV C e (u x))‖) := by
  apply product_relative (PauliMagneticWeighted.constant_nonneg F χ hUV e)
    (fun x => norm_nonneg _) (fun x => norm_nonneg _) (fun x => norm_nonneg _)
  intro x
  exact (quantum_norm_sq F χ hUV C e (u x)).trans
    (mul_le_mul_of_nonneg_left (comparison_radiation_mass_le spectral (u x) (L x) (hL x))
      (PauliMagneticWeighted.constant_nonneg F χ hUV e))


/-- The whole orbital and Zeeman perturbation is infinitesimally bounded
on the finite-spin comparison graph. All terms are the constructed L2 sources. -/
theorem total_comparison_relative
    (a : PhysicalExternalCoefficients.Data N)
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
    (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
    (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    {p : ℝ} (hp : 2 < p) (hBp : ∀ n μ, MemLp (B n μ) (ENNReal.ofReal p) volume)
    (u : X → PauliReference.Ref N) (L : X → SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hL : ∀ x s, IsComparisonPair (fun _ => 0) (u x s) (L x s))
    (P : ∀ x s, PhysicalExternalSource.Products a C κ hκ M hbound e (u x s))
    (hB : ∀ x n μ s, HasMultiplier (coordinateCoefficient n (B n μ))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u x s))) :
    Bound (fun x => ‖FiniteFiberL2.bundle (L x)‖) (fun x => ‖PauliReference.wave (u x)‖)
      (fun x => ‖FiniteFiberL2.bundle (fun s =>
        PhysicalExternalSource.total a C κ hκ M hbound e (u x s) (P x s) +
          PauliMagneticClassicalOperator.zeeman B (u x) (hB x) s +
          PauliMagneticOperator.quantum F χ hUV C e (u x) s)‖) := by
  have ho : Bound (fun x => ‖FiniteFiberL2.bundle (L x)‖)
      (fun x => ‖PauliReference.wave (u x)‖)
      (fun x => ‖FiniteFiberL2.bundle (fun s =>
        PhysicalExternalSource.total a C κ hκ M hbound e (u x s) (P x s))‖) := by
    apply bundle_relative _ (fun x => norm_nonneg _)
    intro s
    apply enlarge_relative (fun x => norm_coordinate_le_bundle (L x) s)
      (fun x => norm_coordinate_le_bundle
        (fun t => inclusion (Fin N × Fin 3) (fun _ => 0) (u x t)) s)
    exact PhysicalExternalRelativeBound.total_comparison_relative a S spectral joint
      C κ hκ M hbound e (fun x => u x s) (fun x => L x s)
      (fun x => hL x s) (fun x => P x s)
  have hc := classical_comparison_relative S spectral joint B hp hBp u L hL hB
  have hq := quantum_comparison_relative F χ hUV C e spectral u L hL
  apply InfinitesimalBound.mono (InfinitesimalBound.add (InfinitesimalBound.add ho hc) hq)
  intro x
  exact norm_bundle_add_add_le (H := PhotonFock)
    (fun s => PhysicalExternalSource.total a C κ hκ M hbound e (u x s) (P x s))
    (PauliMagneticClassicalOperator.zeeman B (u x) (hB x))
    (PauliMagneticOperator.quantum F χ hUV C e (u x))

/-- The free graph norm controls its finite-spin comparison realization. -/
theorem finite_comparison_le
    (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
    (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
    (hG : HaslerHerbstGraphNorm C κ hκ M hbound e)
    (u : PauliReference.Ref N) (g L : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (hg : ∀ s, FreeGraph C κ hκ M hbound e (u s) (g s))
    (hL : ∀ s, IsComparisonPair (fun _ => 0) (u s) (L s)) :
    ‖FiniteFiberL2.bundle L‖ ≤
      (hG.bound * Fintype.card (SpinIndex N)) *
        (‖FiniteFiberL2.bundle g‖ + ‖PauliReference.wave u‖) :=
  finite_comparison_norm (H := PhotonFock)
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) g L hG.bound_nonneg
    (fun s => hG.comparison_le (u s) (g s) (L s) (hg s) (hL s))

end PfHk.PauliMagneticRelative

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
