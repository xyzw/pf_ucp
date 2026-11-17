import PfHk.PauliMagneticOperator
import PfHk.PauliMagneticClassical
import PfHk.PauliCarlemanScalar
import PfHk.PhysicalSourceAbsorption


/-! Classical Zeeman multiplication on the actual electronic L2 space.
Its domain and weighted estimate follow from the physical coordinate
Sobolev theorem for the raw magnetic coefficients. -/

noncomputable section
namespace PfHk.PauliMagneticClassicalOperator

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.SymmetricLift PfHk.PauliSpin PfHk.PhysicalLocalEnergy
  PfHk.PhysicalOperatorDomain PfHk.PhysicalDyadicEnergy PfHk.CoordinateSobolev
  PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

attribute [local irreducible] inclusion roughMultiply PhysicalPFReference.referenceSubspace


private theorem photon_real_smul (a : ℝ) (q : PhotonFock) :
    a • q = (a : ℂ) • q := RCLike.real_smul_eq_coe_smul (K := ℂ) a q

private theorem zeeman_representative {N : ℕ} {X H : Type*}
    [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ν : Measure X) (B : Fin N → Fin 3 → X → ℝ)
    (value : X → SpinIndex N → H) (t : Fin N → Fin 3 → SpinIndex N → Lp H 2 ν)
    (ht : ∀ n μ s, (fun x => t n μ s x) =ᵐ[ν]
      fun x => (B n μ x : ℂ) • value x s) (s : SpinIndex N) :
    (fun x => (((1 / 2 : ℝ) : ℂ) • ∑ n, ∑ μ : Fin 3,
      sigmaFamily n μ (t n μ) s : Lp H 2 ν) x) =ᵐ[ν]
      fun x => PauliMagneticClassical.zeeman (fun n μ => B n μ x) (value x) s := by
  have hn (n : Fin N) :
      (fun x => (∑ μ : Fin 3, sigmaFamily n μ (t n μ) s : Lp H 2 ν) x) =ᵐ[ν]
        fun x => fieldFamily n (fun μ => B n μ x) (value x) s := by
    apply (PauliMagneticOperator.sum_sigma_ae (H := H) ν n (t n)
      (fun μ r x => (B n μ x : ℂ) • value x r) (ht n) s).trans
    apply Filter.EventuallyEq.of_eq
    funext x
    rw [fieldFamily_eq_sum]
    exact Finset.sum_congr rfl (fun μ _ => congrFun
      (sigmaFamily_smul n μ (B n μ x : ℂ) (value x)) s)
  exact PauliMagneticOperator.smul_sum_ae (H := H) ν ((1 / 2 : ℝ) : ℂ)
    (fun n => ∑ μ : Fin 3, sigmaFamily n μ (t n μ) s)
    (fun n x => fieldFamily n (fun μ => B n μ x) (value x) s) hn


private theorem weighted_representative_bound {N : ℕ} {X H : Type*}
    [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ν : Measure X) (B : Fin N → Fin 3 → X → ℝ)
    (value : X → SpinIndex N → H) (t : Fin N → Fin 3 → SpinIndex N → Lp H 2 ν)
    (z : SpinIndex N → Lp H 2 ν) (w : X → ℝ)
    (hw : ∀ᵐ x ∂ν, 0 ≤ w x) (hwm : AEStronglyMeasurable w ν)
    (ht : ∀ n μ s, (fun x => t n μ s x) =ᵐ[ν]
      fun x => (B n μ x : ℂ) • value x s)
    (hz : ∀ s, (fun x => z s x) =ᵐ[ν]
      fun x => PauliMagneticClassical.zeeman (fun n μ => B n μ x) (value x) s)
    (hi : ∀ n μ s, Integrable (fun x => w x * ‖t n μ s x‖ ^ 2) ν) :
    Integrable (fun x => ∑ s, w x * ‖z s x‖ ^ 2) ν ∧
      (∫ x, ∑ s, w x * ‖z s x‖ ^ 2 ∂ν) ≤
        ((N : ℝ) / 4) * ∑ n, ∑ μ : Fin 3, ∑ s, ∫ x, w x * ‖t n μ s x‖ ^ 2 ∂ν := by
  have hrep : (fun x => ∑ s, w x * ‖z s x‖ ^ 2) =ᵐ[ν]
      fun x => w x * ∑ s,
        ‖PauliMagneticClassical.zeeman (fun n μ => B n μ x) (value x) s‖ ^ 2 := by
    filter_upwards [ae_all_iff.mpr hz] with x hx
    simp only [hx, Finset.mul_sum]
  have hm : AEStronglyMeasurable (fun x => ∑ s, w x * ‖z s x‖ ^ 2) ν :=
    Finset.univ.aestronglyMeasurable_fun_sum
      (fun s _ => hwm.mul ((Lp.aestronglyMeasurable (z s)).norm.pow 2))
  have hterms (n : Fin N) (μ : Fin 3) (s : SpinIndex N) :
      (fun x => w x * ‖t n μ s x‖ ^ 2) =ᵐ[ν]
        fun x => w x * ‖(B n μ x : ℂ) • value x s‖ ^ 2 :=
    (ht n μ s).mono (fun x hx => congrArg (fun v : H => w x * ‖v‖ ^ 2) hx)
  have h := PauliMagneticClassical.weighted_source_bound
    (H := H) (N := N) (X := X) (ν := ν) B value w hw
    (hm.congr hrep) (fun n μ s => (hi n μ s).congr (hterms n μ s))
  refine ⟨h.1.congr hrep.symm, ?_⟩
  calc
    _ = ∫ x, w x * ∑ s,
        ‖PauliMagneticClassical.zeeman (fun n μ => B n μ x) (value x) s‖ ^ 2 ∂ν :=
      integral_congr_ae hrep
    _ ≤ _ := h.2
    _ = _ := congrArg (fun r : ℝ => ((N : ℝ) / 4) * r)
      (Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun μ _ =>
        Finset.sum_congr rfl (fun s _ => (integral_congr_ae (hterms n μ s)).symm))))


private theorem sum_source_bound {N : ℕ} {S : Type*} [Fintype S]
    (g : Fin N → Fin 3 → S → ℝ) (K : Fin N → Fin 3 → ℝ) (f : S → ℝ)
    (h : ∀ n μ s, g n μ s ≤ K n μ * f s) :
    ((N : ℝ) / 4) * (∑ n, ∑ μ : Fin 3, ∑ s, g n μ s) ≤
      ((N : ℝ) / 4) * (∑ n, ∑ μ : Fin 3, K n μ) * ∑ s, f s := by
  have hs : (∑ n : Fin N, ∑ μ : Fin 3, ∑ s : S, g n μ s) ≤
      ∑ n : Fin N, ∑ μ : Fin 3, ∑ s : S, K n μ * f s :=
    Finset.sum_le_sum (s := Finset.univ) (fun n _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun μ _ =>
        Finset.sum_le_sum (s := Finset.univ) (fun s _ => h n μ s)))
  exact (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (N : ℝ) / 4)).trans_eq
    (by simp only [← Finset.mul_sum, ← Finset.sum_mul]; ring)


variable {N : ℕ} (B : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
  (u : PauliReference.Ref N)
  (hB : ∀ n μ s, HasMultiplier (coordinateCoefficient n (B n μ))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))

def term (n : Fin N) (μ : Fin 3) (s : SpinIndex N) : WaveSpace (Fin N × Fin 3) :=
  roughMultiply (coordinateCoefficient n (B n μ))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hB n μ s)

def zeeman (s : SpinIndex N) : WaveSpace (Fin N × Fin 3) :=
  ((1 / 2 : ℝ) : ℂ) • ∑ n, ∑ μ : Fin 3, sigmaFamily n μ (term B u hB n μ) s


theorem term_ae (n : Fin N) (μ : Fin 3) (s : SpinIndex N) :
    term B u hB n μ s =ᵐ[volume] fun X : Configuration N =>
      (coordinateCoefficient n (B n μ) X : ℂ) •
        inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X := by
  unfold term
  exact (roughMultiply_ae (coordinateCoefficient n (B n μ))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hB n μ s)).trans
      (ae_of_all _ fun X => photon_real_smul _ _)

theorem zeeman_ae (s : SpinIndex N) :
    zeeman B u hB s =ᵐ[volume] fun X =>
      PauliMagneticClassical.zeeman (fun n μ => coordinateCoefficient n (B n μ) X)
        (fun t => inclusion (Fin N × Fin 3) (fun _ => 0) (u t) X) s := by
  unfold zeeman
  exact zeeman_representative (H := PhotonFock) (X := Configuration N) volume
    (fun n μ X => coordinateCoefficient n (B n μ) X)
    (fun X s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
    (term B u hB) (term_ae B u hB) s

attribute [local irreducible] zeeman


/-- Weighted L2 control by the actual coordinate scalar products. -/
theorem weighted_bound (O : Configuration N) (τ α : ℝ)
    (hi : ∀ n μ s, Integrable (sourceEnergy O τ α (term B u hB n μ s))) :
    Integrable (fun X => ∑ s, sourceEnergy O τ α (zeeman B u hB s) X) ∧
      (∫ X, ∑ s, sourceEnergy O τ α (zeeman B u hB s) X) ≤
        ((N : ℝ) / 4) * ∑ n, ∑ μ : Fin 3, ∑ s,
          ∫ X, sourceEnergy O τ α (term B u hB n μ s) X := by
  exact weighted_representative_bound (H := PhotonFock) (X := Configuration N) volume
    (fun n μ X => coordinateCoefficient n (B n μ) X)
    (fun X s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
    (term B u hB) (zeeman B u hB) (centeredSourceWeight O τ α)
    (ae_of_all _ (PhysicalSourceAbsorption.centeredSourceWeight_nonneg O τ α))
    (PhysicalSourceAbsorption.centeredSourceWeight_measurable O τ α).aestronglyMeasurable
    (term_ae B u hB) (zeeman_ae B u hB) hi


attribute [local irreducible] IsComparisonPair PhysicalMixedSeries.Bound
  PhysicalFractionalCarleman.localized PhysicalCoordinateMultipliers.coefficientNormSq

/-- The classical magnetic perturbation estimate from raw one-body Lp
coefficients. The comparison-domain multipliers are constructed here. -/
theorem physical_bound
    (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    {p : ℝ} (hp : 2 < p)
    (hBp : ∀ n μ, MemLp (B n μ) (ENNReal.ofReal p) volume)
    {O : Configuration N} (family : BufferedFamily O)
    {R τ α σ C₀ C₂ : ℝ} (source : SpinIndex N → ℝ)
    (hR : 0 < R) (hsmall : 2 * R ≤ Real.exp (-2)) (hτ : 0 < τ)
    (hα : 0 < α) (hσ : 0 ≤ σ)
    (hu : ∀ s : SpinIndex N, ∃ v : WaveSpace (Fin N × Fin 3),
      IsComparisonPair (I := Fin N × Fin 3) (fun _ => 0) (u s) v)
    (hsupp : ∀ s : SpinIndex N, PhysicalCarlemanInput.AnnularSupport
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R)
    (hmixed : ∀ s : SpinIndex N, PhysicalMixedSeries.Bound (N := N) spectral
      (PhysicalFractionalCarleman.localized (N := N) family R hR τ α (u s))
      (dyadicBeta α R) (radius R) τ C₀ C₂ (source s))
    (hratio : ∀ j, radius R j ^ (4 - 2 * (3 / p)) / dyadicBeta α R j ≤ σ) :
    ∃ hB : ∀ (n : Fin N) (μ : Fin 3) (s : SpinIndex N), HasMultiplier (coordinateCoefficient n (B n μ))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)),
      Integrable (fun X : Configuration N => ∑ s : SpinIndex N, sourceEnergy O τ α (zeeman B u hB s) X) ∧
      (∫ X : Configuration N, ∑ s : SpinIndex N, sourceEnergy O τ α (zeeman B u hB s) X) ≤
        ((N : ℝ) / 4) *
          (∑ n, ∑ μ : Fin 3, 12 * PhysicalCoordinateMultipliers.coefficientNormSq S p (B n μ) * σ *
            τ ^ (-(3 - 2 * (3 / p))) *
              (((3 / p) / 2) * C₂ + (1 - (3 / p) / 2) * C₀)) * ∑ s, source s := by
  have hscalar (n : Fin N) (μ : Fin 3) (s : SpinIndex N) :=
    PauliCarlemanScalar.coordinate_source_bound (N := N) (p := p) (O := O)
      (R := R) (τ := τ) (α := α) (σ := σ) (C₀ := C₀) (C₂ := C₂) (source := source s)
      S spectral joint hp n (B n μ)
      (hBp n μ) family hR hsmall hτ hα hσ (u s) (hu s) (hsupp s) (hmixed s) hratio
  choose hB hi hb using hscalar
  have hti (n : Fin N) (μ : Fin 3) (s : SpinIndex N) :
      Integrable (sourceEnergy O τ α (term B u hB n μ s)) := by
    unfold term
    exact hi n μ s
  have hweight :
      Integrable (fun X : Configuration N => ∑ s : SpinIndex N,
        sourceEnergy O τ α (zeeman B u hB s) X) ∧
        (∫ X : Configuration N, ∑ s : SpinIndex N,
          sourceEnergy O τ α (zeeman B u hB s) X) ≤
          ((N : ℝ) / 4) * ∑ n : Fin N, ∑ μ : Fin 3, ∑ s : SpinIndex N,
            ∫ X : Configuration N, sourceEnergy O τ α (term B u hB n μ s) X :=
    PfHk.PauliMagneticClassicalOperator.weighted_bound
      (N := N) (B := B) (u := u) (hB := hB) (O := O) (τ := τ) (α := α) (hi := hti)
  refine ⟨hB, hweight.1, hweight.2.trans ?_⟩
  exact sum_source_bound
    (fun n μ s => ∫ X, sourceEnergy O τ α (term B u hB n μ s) X)
    (fun n μ => 12 * PhysicalCoordinateMultipliers.coefficientNormSq S p (B n μ) * σ *
      τ ^ (-(3 - 2 * (3 / p))) * (((3 / p) / 2) * C₂ + (1 - (3 / p) / 2) * C₀))
    source (fun n μ s => by
      unfold term
      exact hb n μ s)


end PfHk.PauliMagneticClassicalOperator

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
