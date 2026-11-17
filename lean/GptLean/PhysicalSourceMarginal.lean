import GptLean.PhysicalSourceWeakTests
import GptLean.PhysicalSourceCoordinates
import GptLean.PhysicalPairH1Sobolev

/-!
An actual many-particle H1 wave function gives a Hilbert-valued H1 source
for each selected particle. Coordinate splitting is measure preserving,
Fubini is the constructed L2 isometry, and the weak derivative identity
is derived directly with compact product tests. Thus marginal L6
membership is a theorem rather than a source regularity premise.
-/

noncomputable section

namespace GptLean.PhysicalSourceMarginal

set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter GptLean.SymmetricLift GptLean.ElectronicH1Space
open GptLean.PhysicalSourceFubini GptLean.PhysicalSourceH1
open scoped ENNReal Topology ContDiff

variable {I K J H : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (e : Position I ≃L[ℝ] Position K × Position J)
  (he : MeasurePreserving e.symm
    ((volume : Measure (Position K)).prod (volume : Measure (Position J))) volume)

def productMap : L2 H I →ₗᵢ[ℂ]
    Lp H 2 ((volume : Measure (Position K)).prod (volume : Measure (Position J))) :=
  Lp.compMeasurePreservingₗᵢ ℂ e.symm he

def sourceMap : L2 H I →ₗᵢ[ℂ] L2 (Lp H 2 (volume : Measure (Position J))) K :=
  curryIsometry.comp (productMap e he)

omit [DecidableEq I] [DecidableEq K]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem productMap_test_integral (v : L2 H I) (t : Position K × Position J → ℝ) :
    (∫ p, t p • productMap e he v p) = ∫ z, t (e z) • v z := by
  calc
    _ = ∫ p, t (e (e.symm p)) • v (e.symm p) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_compMeasurePreserving v he] with p hp
      change t p • (Lp.compMeasurePreserving e.symm he v) p = _
      rw [hp]
      simp
    _ = _ := he.integral_comp e.symm.toHomeomorph.measurableEmbedding
      (fun z => t (e z) • v z)

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem testProduct_fderiv (pick : K → I)
    (hdir : ∀ a, e (EuclideanSpace.single (pick a) 1) = (EuclideanSpace.single a 1, 0))
    (a : K) (φ : Position K → ℝ) (ψ : Position J → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (z : Position I) :
    fderiv ℝ (fun w => testProduct φ ψ (e w)) z (EuclideanSpace.single (pick a) 1) =
      testProduct (fun x => fderiv ℝ φ x (EuclideanSpace.single a 1)) ψ (e z) := by
  have hf := (hφ.differentiable (by simp) (e z).1).hasFDerivAt.comp z e.hasFDerivAt.fst
  have hg := (hψ.differentiable (by simp) (e z).2).hasFDerivAt.comp z e.hasFDerivAt.snd
  have hm := (hf.mul hg).fderiv
  change fderiv ℝ ((φ ∘ fun x => (e x).1) * (ψ ∘ fun x => (e x).2)) z _ = _
  rw [hm]
  simp [testProduct, hdir a, mul_comm]

/-- The full electronic weak identity transports to the selected-coordinate source. -/
theorem sourceMap_weak (pick : K → I)
    (hdir : ∀ a, e (EuclideanSpace.single (pick a) 1) = (EuclideanSpace.single a 1, 0))
    (u : H1 H I) :
    HasWeakH1Local (sourceMap e he (value u))
      (fun a => sourceMap e he (derivative (pick a) u)) := by
  apply weakH1_curry_of_product_tests
  intro a φ ψ hφ hφs hψ hψs
  change (∫ p, testProduct φ ψ p • productMap e he (derivative (pick a) u) p) =
    -(∫ p, testProduct (fun x => fderiv ℝ φ x (EuclideanSpace.single a 1)) ψ p •
      productMap e he (value u) p)
  rw [productMap_test_integral e he, productMap_test_integral e he]
  have htest : ContDiff ℝ ∞ (fun z => testProduct φ ψ (e z)) :=
    ((hφ.comp contDiff_fst).mul (hψ.comp contDiff_snd)).comp e.contDiff
  have hcompact : HasCompactSupport (fun z => testProduct φ ψ (e z)) :=
    (testProduct_compact hφs hψs).comp_homeomorph e.toHomeomorph
  have hw := (weak u).weak (pick a) _ htest hcompact
  simpa only [testProduct_fderiv e pick hdir a φ ψ hφ hψ] using hw

def ofSplitH1 (pick : K → I)
    (hdir : ∀ a, e (EuclideanSpace.single (pick a) 1) = (EuclideanSpace.single a 1, 0))
    (u : H1 H I) : H1 (Lp H 2 (volume : Measure (Position J))) K :=
  ⟨(sourceMap e he (value u), fun a => sourceMap e he (derivative (pick a) u)),
    sourceMap_weak e he pick hdir u⟩

@[simp] theorem value_ofSplitH1 (pick : K → I)
    (hdir : ∀ a, e (EuclideanSpace.single (pick a) 1) = (EuclideanSpace.single a 1, 0))
    (u : H1 H I) : value (ofSplitH1 e he pick hdir u) = sourceMap e he (value u) := rfl

@[simp] theorem derivative_ofSplitH1 (pick : K → I)
    (hdir : ∀ a, e (EuclideanSpace.single (pick a) 1) = (EuclideanSpace.single a 1, 0))
    (u : H1 H I) (a : K) :
    derivative a (ofSplitH1 e he pick hdir u) = sourceMap e he (derivative (pick a) u) := rfl

end GptLean.PhysicalSourceMarginal

namespace GptLean.PhysicalSourceMarginal

open MeasureTheory GptLean.ElectronicH1Space GptLean.PhysicalSourceCoordinates
open scoped ENNReal

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- The physical L2 source map for any selected particle of the actual configuration space. -/
def particleMap (i : Fin N) : L2 H (Fin N × Fin 3) →ₗᵢ[ℂ]
    L2 (Lp H 2 (volume : Measure (Spectator i))) (Fin 3) :=
  sourceMap (split i) (split_symm_measurePreserving i)

/-- The actual marginal H1 source, with no independent regularity input. -/
def particleSource (i : Fin N) (u : H1 H (Fin N × Fin 3)) :
    H1 (Lp H 2 (volume : Measure (Spectator i))) (Fin 3) :=
  ofSplitH1 (split i) (split_symm_measurePreserving i) (fun a => (i, a))
    (split_single_selected i) u

@[simp] theorem value_particleSource (i : Fin N) (u : H1 H (Fin N × Fin 3)) :
    value (particleSource i u) = particleMap i (value u) := rfl

@[simp] theorem derivative_particleSource (i : Fin N) (u : H1 H (Fin N × Fin 3)) (a : Fin 3) :
    derivative a (particleSource i u) = particleMap i (derivative (i, a) u) := rfl

theorem norm_value_particleSource (i : Fin N) (u : H1 H (Fin N × Fin 3)) :
    ‖value (particleSource i u)‖ = ‖value u‖ := (particleMap i).norm_map _

theorem norm_derivative_particleSource (i : Fin N) (u : H1 H (Fin N × Fin 3)) (a : Fin 3) :
    ‖derivative a (particleSource i u)‖ = ‖derivative (i, a) u‖ := (particleMap i).norm_map _

/-- Sobolev membership of the actual particle source follows from the full H1 wave function. -/
theorem particleSource_memLp_six (i : Fin N) (u : H1 H (Fin N × Fin 3)) :
    MemLp (value (particleSource i u)) 6 volume := by
  let := InnerProductSpace.rclikeToReal ℂ (Lp H 2 (volume : Measure (Spectator i)))
  exact PhysicalPairH1Sobolev.value_memLp_six (particleSource i u)

end GptLean.PhysicalSourceMarginal
