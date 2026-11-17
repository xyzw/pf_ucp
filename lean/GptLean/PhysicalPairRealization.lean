import GptLean.PhysicalPairSpace
import GptLean.PhysicalPairIntegrability
import GptLean.PhysicalPairSobolev
import GptLean.RemovalPhysicalPair

/-!
Physical density-current pairs constructed in the article's exact Banach
space from Hilbert-valued source functions and their covariant derivatives.
The full-domain constructor obtains L6 source membership from the proved
Sobolev core passage. Almost-everywhere conservation transports directly
to equality in the intersection spaces, including both stronger norms.
-/

noncomputable section

namespace GptLean.PhysicalPairRealization

open MeasureTheory Filter
open scoped ENNReal NNReal
open PhysicalPairSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The actual marginal density and combined current as one Banach-space
element, with all four integrability obligations discharged by Holder. -/
def ofSource (N : ℕ) (u : Position → H) (d : Fin 3 → Position → H)
    (hu₂ : MemLp u 2 volume) (hu₆ : MemLp u 6 volume)
    (hd : ∀ i, MemLp (d i) 2 volume) : Pair :=
  ofFunctions (PhysicalPairIntegrability.density N u)
    (PhysicalPairIntegrability.current N u d)
    (PhysicalPairIntegrability.density_memLp_one N hu₂)
    (PhysicalPairIntegrability.density_memLp_three N hu₆)
    (PhysicalPairIntegrability.current_memLp_one N hu₂ hd)
    (PhysicalPairIntegrability.current_memLp_three_halves N hu₆ hd)

theorem density_ofSource_ae (N : ℕ) (u : Position → H) (d : Fin 3 → Position → H)
    (hu₂ : MemLp u 2 volume) (hu₆ : MemLp u 6 volume)
    (hd : ∀ i, MemLp (d i) 2 volume) :
    (densityL1 (ofSource N u d hu₂ hu₆ hd) : Position → ℝ) =ᵐ[volume]
      PhysicalPairIntegrability.density N u :=
  (PhysicalPairIntegrability.density_memLp_one N hu₂).coeFn_toLp

theorem current_ofSource_ae (N : ℕ) (u : Position → H) (d : Fin 3 → Position → H)
    (hu₂ : MemLp u 2 volume) (hu₆ : MemLp u 6 volume)
    (hd : ∀ i, MemLp (d i) 2 volume) :
    (currentL1 (ofSource N u d hu₂ hu₆ hd) : Position → Vector) =ᵐ[volume]
      PhysicalPairIntegrability.current N u d :=
  (PhysicalPairIntegrability.current_memLp_one N hu₂ hd).coeFn_toLp

/-- Conservation of the physical functions is equality of the full pair,
not only equality after forgetting the L3 and L(3/2) memberships. -/
theorem ofSource_eq_of_ae (N : ℕ)
    (u v : Position → H) (d e : Fin 3 → Position → H)
    (hu₂ : MemLp u 2 volume) (hu₆ : MemLp u 6 volume)
    (hv₂ : MemLp v 2 volume) (hv₆ : MemLp v 6 volume)
    (hd : ∀ i, MemLp (d i) 2 volume) (he : ∀ i, MemLp (e i) 2 volume)
    (hρ : PhysicalPairIntegrability.density N u =ᵐ[volume]
      PhysicalPairIntegrability.density N v)
    (hj : PhysicalPairIntegrability.current N u d =ᵐ[volume]
      PhysicalPairIntegrability.current N v e) :
    ofSource N u d hu₂ hu₆ hd = ofSource N v e hv₂ hv₆ he := by
  apply Prod.ext
  · apply PhysicalPairSpace.ext_ae
    exact (density_ofSource_ae N u d hu₂ hu₆ hd).trans
      (hρ.trans (density_ofSource_ae N v e hv₂ hv₆ he).symm)
  · apply PhysicalPairSpace.ext_ae
    exact (current_ofSource_ae N u d hu₂ hu₆ hd).trans
      (hj.trans (current_ofSource_ae N v e hv₂ hv₆ he).symm)

section ReferenceDomain

variable [InnerProductSpace ℝ H]
  {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  (inclusion : Q →L[ℝ] Lp H 2 (volume : Measure Position))
  (core : Set Q) (hdense : Dense core)
  (representative : Q → Position → H)
  (hrep : ∀ q ∈ core, representative q =ᵐ[volume] inclusion q)
  (hsmooth : ∀ q ∈ core, ContDiff ℝ 1 (representative q))
  (hcompact : ∀ q ∈ core, HasCompactSupport (representative q))
  (C : ℝ≥0)
  (hderivative : ∀ q ∈ core,
    eLpNorm (fderiv ℝ (representative q)) 2 volume ≤ C * ENNReal.ofReal ‖q‖)

/-- Every vector in the reference domain gives an article-space pair.
L6 membership is a conclusion of smooth-core density and Sobolev. -/
def ofReference (N : ℕ) (q : Q) (d : Fin 3 → Lp H 2 (volume : Measure Position)) : Pair :=
  ofSource N (inclusion q) (fun i => d i) (Lp.memLp _)
    (PhysicalPairSobolev.memLp_six_of_dense_core inclusion core hdense representative
      hrep hsmooth hcompact C hderivative q)
    (fun i => Lp.memLp (d i))

end ReferenceDomain

end GptLean.PhysicalPairRealization
