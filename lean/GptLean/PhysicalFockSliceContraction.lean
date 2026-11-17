import GptLean.PhysicalFockSlices
import GptLean.PhysicalFockTailPermutation

/-!
Annihilation norms expressed through the actual one-photon slices.

The scalar tail expansion is Parseval for the full insertion adjoint.
The symmetric-tail theorem then identifies this adjoint with the already
constructed sector annihilation operator, including its normalization.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

section Generic
variable {X H ι : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (e : ι ↪ ℕ)

theorem coefficient_inner_hasSum (f : H) (u : Lp H 2 μ) :
    HasSum (fun a => ‖⟪f, PhysicalL2HilbertSum.countableCoefficients b e u a⟫_ℂ‖ ^ 2)
      (‖(PhysicalL2HilbertSum.tensor.flip f).adjoint u‖ ^ 2) := by
  let z := (PhysicalL2HilbertSum.tensor.flip f).adjoint u
  let c := PhysicalL2HilbertSum.padding e (b.repr z)
  have hc (a : ℕ) : c a =
      ⟪f, PhysicalL2HilbertSum.countableCoefficients b e u a⟫_ℂ := by
    classical
    by_cases ha : a ∈ Set.range e
    · obtain ⟨i, rfl⟩ := ha
      change PhysicalL2HilbertSum.padding e (b.repr z) (e i) =
        ⟪f, PhysicalL2HilbertSum.padding e (PhysicalL2HilbertSum.coefficients b u) (e i)⟫_ℂ
      rw [PhysicalL2HilbertSum.padding_at, PhysicalL2HilbertSum.padding_at,
        b.repr_apply_apply, PhysicalL2HilbertSum.coefficients_inner]
      exact (PhysicalL2HilbertSum.tensor.flip f).adjoint_inner_right (b i) u
    · change PhysicalL2HilbertSum.padding e (b.repr z) a =
        ⟪f, PhysicalL2HilbertSum.padding e (PhysicalL2HilbertSum.coefficients b u) a⟫_ℂ
      rw [PhysicalL2HilbertSum.padding_off e _ a ha,
        PhysicalL2HilbertSum.padding_off e _ a ha, inner_zero_right]
  have hs := coordinate_mass_hasSum (fun _ : ℕ => ℂ) c
  have hn : ‖c‖ = ‖z‖ := (PhysicalL2HilbertSum.padding e).norm_map (b.repr z) |>.trans
    (b.repr.norm_map z)
  simpa only [hc, hn] using hs

end Generic

theorem onePhotonSections_tensorInsertion (n : ℕ) (f : Lp ℂ 2 photonMeasure)
    (v : FullSector photonMeasure n) :
    onePhotonSections n (tensorInsertion photonMeasure n f v) =
      PhysicalL2HilbertSum.tensor v f := by
  let P : FullSector photonMeasure (n + 1) →ₗᵢ[ℂ]
      Lp ℂ 2 ((SectorMeasure photonMeasure n).prod photonMeasure) :=
    Lp.compMeasurePreservingₗᵢ ℂ (tailHeadCoordinates n)
    (tailHeadCoordinates_measurePreserving n)
  have hp : P (tensorInsertion photonMeasure n f v) =ᵐ[
      (SectorMeasure photonMeasure n).prod photonMeasure] fun z => f z.2 * v z.1 := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (tensorInsertion photonMeasure n f v)
      (tailHeadCoordinates_measurePreserving n),
      (tailHeadCoordinates_measurePreserving n).quasiMeasurePreserving.ae
        (tensorInsertion_ae photonMeasure n f v)] with z hP hT
    exact hP.trans (by simpa [tailHeadCoordinates, MeasurableEquiv.prodComm,
      MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using hT)
  have hc := PhysicalSourceFubini.curryEquiv_represents_ae
    (P (tensorInsertion photonMeasure n f v))
  apply Lp.ext
  filter_upwards [hc, Measure.ae_ae_of_ae_prod hp, PhysicalL2HilbertSum.tensor_ae v f]
    with x hx hP ht
  change PhysicalSourceFubini.curryEquiv (P (tensorInsertion photonMeasure n f v)) x = _
  rw [ht]
  apply Lp.ext
  filter_upwards [hx, hP, Lp.coeFn_smul (v x) f] with p hc hp hs
  rw [hc, hp, hs, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem onePhotonSections_contraction (n : ℕ) (f : Lp ℂ 2 photonMeasure)
    (u : FullSector photonMeasure (n + 1)) :
    (PhysicalL2HilbertSum.tensor.flip f).adjoint (onePhotonSections n u) =
      (tensorInsertion photonMeasure n f).adjoint u := by
  apply ext_inner_left ℂ
  intro v
  rw [(PhysicalL2HilbertSum.tensor.flip f).adjoint_inner_right,
    (tensorInsertion photonMeasure n f).adjoint_inner_right]
  have hi := (onePhotonSections n).inner_map_map (tensorInsertion photonMeasure n f v) u
  rw [onePhotonSections_tensorInsertion] at hi
  exact hi

/-- Exact Parseval formula for actual sector annihilation and the concrete head slices. -/
theorem annihilationSector_slices_hasSum (n : ℕ) (f : Lp ℂ 2 photonMeasure)
    (u : Sector photonMeasure (n + 1)) :
    HasSum (fun a => (n + 1 : ℝ) * ‖⟪f, onePhotonSlices n u a⟫_ℂ‖ ^ 2)
      (‖annihilationSector photonMeasure n f u‖ ^ 2) := by
  have h := (coefficient_inner_hasSum
    (PhysicalL2HilbertSum.spatialBasis (SectorMeasure photonMeasure n))
    (PhysicalL2HilbertSum.spatialIndexEmbedding (SectorMeasure photonMeasure n))
    f (onePhotonSections n u.val)).mul_left (n + 1 : ℝ)
  rw [onePhotonSections_contraction,
    ← annihilationSector_norm_sq_tensorContraction photonMeasure n f u] at h
  exact h

end GptLean.PhysicalFock
