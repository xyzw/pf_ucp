import GptLean.Repair.CovariantProduct

/-!
An explicit isometric enlargement into the standard countable Hilbert
space resolves the finite-dimensional basis issue in the trace channel.
A finite-dimensional repair target need not possess a basis indexed by
the natural numbers. Its given basis is embedded into the standard basis
of ℓ²(ℕ, ℂ), and the resulting fixed isometry transports the lift and its
weak derivatives without changing norm, connection or derivative metric.
-/

noncomputable section

namespace GptLean.Repair

open MeasureTheory GptLean.SymmetricLift
open scoped ENNReal ContDiff lp

/-- The standard target of the natural-number indexed channel. -/
abbrev CountableTarget := ℓ²(ℕ, ℂ)

/-- Its genuine natural-number indexed Hilbert basis. -/
def countableTargetBasis : HilbertBasis ℕ ℂ CountableTarget :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- A countable original index set has an explicit chosen embedding into
the natural numbers. This includes finite index sets. -/
def countableIndexEmbedding (ι : Type*) [Countable ι] : ι ↪ ℕ :=
  ⟨Classical.choose (exists_injective_nat ι),
    Classical.choose_spec (exists_injective_nat ι)⟩

variable {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Embed the basis into the countable standard basis and extend by the
orthogonal-series isometry. No infinite basis on the original target is
assumed. -/
def countableEmbedding (b : HilbertBasis ι ℂ V) (e : ι ↪ ℕ) :
    V →ₗᵢ[ℂ] CountableTarget :=
  ((countableTargetBasis.orthonormal.comp e e.injective).orthogonalFamily.linearIsometry).comp
    b.repr.toLinearIsometry

@[simp]
theorem countableEmbedding_norm (b : HilbertBasis ι ℂ V) (e : ι ↪ ℕ) (v : V) :
    ‖countableEmbedding b e v‖ = ‖v‖ :=
  (countableEmbedding b e).norm_map v

@[simp]
theorem countableEmbedding_inner (b : HilbertBasis ι ℂ V) (e : ι ↪ ℕ) (v w : V) :
    inner ℂ (countableEmbedding b e v) (countableEmbedding b e w) = inner ℂ v w :=
  (countableEmbedding b e).inner_map_map v w

/-- Original basis vectors occupy the selected standard coordinates. -/
theorem countableEmbedding_basis (b : HilbertBasis ι ℂ V) (e : ι ↪ ℕ) (i : ι) :
    countableEmbedding b e (b i) = countableTargetBasis (e i) := by
  classical
  change ((countableTargetBasis.orthonormal.comp e e.injective).orthogonalFamily.linearIsometry)
    (b.repr (b i)) = countableTargetBasis (e i)
  rw [b.repr_self, OrthogonalFamily.linearIsometry_apply_single]
  simp only [LinearIsometry.toSpanSingleton_apply, one_smul, Function.comp_apply]

/-- At the embedded indices the scalar multipliers are unchanged. -/
theorem countableEmbedding_coordinate (b : HilbertBasis ι ℂ V) (e : ι ↪ ℕ)
    (v : V) (i : ι) :
    coordinate countableTargetBasis (countableEmbedding b e v) (e i) = coordinate b v i := by
  unfold coordinate
  rw [← countableEmbedding_basis b e i, countableEmbedding_inner]

/-- The complete derivative metric is unchanged by the fixed embedding. -/
theorem countableEmbedding_metric {J : Type*} [Fintype J]
    (b : HilbertBasis ι ℂ V) (e : ι ↪ ℕ) (g : J → V) :
    (∑ j, ‖countableEmbedding b e (g j)‖ ^ 2) = ∑ j, ‖g j‖ ^ 2 := by
  simp only [countableEmbedding_norm]

/-- Joint or sectionwise measurability is transported by the same fixed
continuous isometry. -/
theorem countableEmbedding_aestronglyMeasurable
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (b : HilbertBasis ι ℂ V) (e : ι ↪ ℕ) {z : X → V}
    (hz : AEStronglyMeasurable z μ) :
    AEStronglyMeasurable (fun x => countableEmbedding b e (z x)) μ :=
  (countableEmbedding b e).continuous.comp_aestronglyMeasurable hz

variable [CompleteSpace V]

/-- The padding map preserves the actual compact-test weak derivative.
The new derivative is its image under a fixed linear map, with no spatial
derivative of the embedding. -/
theorem countableEmbedding_hasWeakH1Local
    {I : Type*} [Fintype I] [DecidableEq I]
    (b : HilbertBasis ι ℂ V) (e : ι ↪ ℕ)
    {z : EuclideanSpace ℝ I → V} {dz : I → EuclideanSpace ℝ I → V}
    (hz : HasWeakH1Local z dz) :
    HasWeakH1Local (fun x => countableEmbedding b e (z x))
      (fun i x => countableEmbedding b e (dz i x)) :=
  weakH1Local_map ((countableEmbedding b e).toContinuousLinearMap.restrictScalars ℝ) hz

omit [CompleteSpace V] in
/-- Natural-number indexed coordinates of the enlarged target retain the
normalization required by the actual integrated channel. -/
theorem countableEmbedding_normalization
    (b : HilbertBasis ι ℂ V) (e : ι ↪ ℕ) {z : V} (hz : ‖z‖ = 1) :
    HasSum (fun a => ‖coordinate countableTargetBasis (countableEmbedding b e z) a‖ ^ 2) 1 :=
  coordinate_normalization countableTargetBasis ((countableEmbedding_norm b e z).trans hz)

omit [CompleteSpace V] in
/-- The prescribed connection is also retained in the natural-number
coordinate series. -/
theorem countableEmbedding_connection
    (b : HilbertBasis ι ℂ V) (e : ι ↪ ℕ) {z dz : V} {s : ℝ}
    (hconn : inner ℂ z dz = Complex.I * s) :
    HasSum (fun a => starRingEnd ℂ (coordinate countableTargetBasis (countableEmbedding b e z) a) *
      coordinate countableTargetBasis (countableEmbedding b e dz) a) (Complex.I * s) :=
  coordinate_connection countableTargetBasis ((countableEmbedding_inner b e z dz).trans hconn)

end GptLean.Repair
