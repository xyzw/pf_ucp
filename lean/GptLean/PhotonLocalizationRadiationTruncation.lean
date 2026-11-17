import GptLean.PhotonLocalizationFormBoundsFock
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Increasing radiation truncations on one common complete family.

The basis is fixed before the truncation rank. Positive sector and source
sums preserve monotone recovery, including infinite radiation energy.
The one-photon spectral identification remains ordinary form background.
-/

namespace GptLean.PhotonLocalizationFormBounds

open MeasureTheory
open scoped ENNReal InnerProductSpace

/-- Monotone recovery commutes with a countable nonnegative sum. -/
theorem tsum_iSup_monotone {α : Type*} [Countable α]
    (f : ℕ → α → ℝ≥0∞) (hf : ∀ a, Monotone (fun k => f k a)) :
    (∑' a, ⨆ k, f k a) = ⨆ k, ∑' a, f k a := by
  let : MeasurableSpace α := ⊤
  have : MeasurableSingletonClass α := ⟨fun _ => trivial⟩
  simpa only [lintegral_count] using
    lintegral_iSup (μ := Measure.count) (fun k => measurable_of_countable (f k))
      (fun k l hkl a => hf a hkl)

/-- The complete basis yields the actual square-norm expansion. A separate
orthonormal family for each rank would not supply this identity. -/
theorem hilbertBasis_radiation_expansion {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (b : HilbertBasis ℕ ℂ V) (v : V) :
    ENNReal.ofReal (‖v‖ ^ 2) = ∑' i, ENNReal.ofReal (‖⟪b i, v⟫_ℂ‖ ^ 2) := by
  have hs : HasSum (fun i => ‖⟪b i, v⟫_ℂ‖ ^ 2) (‖v‖ ^ 2) := by
    simpa only [HilbertBasis.repr_apply_apply, ENNReal.toReal_ofNat, Real.rpow_two,
      LinearIsometryEquiv.norm_map] using
      lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (b.repr v)
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hs.summable]

variable {V : Type*}

/-- Finite ranks always use the first coordinates of the same family. -/
noncomputable def radiationPartial (coefficient : ℕ → V → ℂ) (k : ℕ) (u : V) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range k, ENNReal.ofReal (‖coefficient i u‖ ^ 2)

theorem radiationPartial_monotone (coefficient : ℕ → V → ℂ) (u : V) :
    Monotone (fun k => radiationPartial coefficient k u) := by
  intro k l hkl
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hkl)

theorem radiationPartial_iSup (coefficient : ℕ → V → ℂ) (u : V) :
    (⨆ k, radiationPartial coefficient k u) =
      ∑' i, ENNReal.ofReal (‖coefficient i u‖ ^ 2) := by
  exact ENNReal.tsum_eq_iSup_nat.symm

/-- Increasing one-photon forms recover their full Fock form through all
three sums, without requiring a finite photon-number expectation. -/
theorem fockForm_iSup (q : ℕ → V → ℝ≥0∞)
    (hq : ∀ u, Monotone (fun k => q k u))
    (slice : (m : ℕ) → Fin m → ℕ → V) :
    fockForm (fun u => ⨆ k, q k u) slice = ⨆ k, fockForm (q k) slice := by
  unfold fockForm sectorForm
  simp_rw [tsum_iSup_monotone _ (fun a => hq _)]
  have hsector (m : ℕ) :
      (∑ i : Fin m, ⨆ k, ∑' a, q k (slice m i a)) =
        ⨆ k, ∑ i : Fin m, ∑' a, q k (slice m i a) := by
    apply ENNReal.finsetSum_iSup_of_monotone
    intro i k l hkl
    exact ENNReal.tsum_le_tsum fun a => hq _ hkl
  simp_rw [hsector]
  apply tsum_iSup_monotone
  intro m k l hkl
  exact Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun a => hq _ hkl

section Normal

open PhotonLocalizationChannel PhotonLocalizationFockChannel

variable {h H X Q : Type*}
  [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {A : Gaussian.RankOneData H X} {Tr : RemovalState.PositiveTraceData X}
  {F : FockFactorization h H}

omit [CompleteSpace X] in
/-- The common one-photon coordinate expansion recovers the full radiation
expectation of every positive normal operator, including infinite values. -/
theorem FockFormCalculus.radiation_eq_iSup
    (D : FockFormCalculus A Tr F Q) (N : NormalTraceData A)
    (hpositive : A.positive ⊆ Tr.positive)
    (radiation : Q) (truncation : ℕ → Q) (coefficient : ℕ → h → ℂ)
    (hfull : ∀ u, D.value radiation u =
      ∑' i, ENNReal.ofReal (‖coefficient i u‖ ^ 2))
    (htruncation : ∀ k u, D.value (truncation k) u = radiationPartial coefficient k u)
    {x : X} (hx : x ∈ A.positive) :
    (D.observable radiation).expectation x =
      ⨆ k, (D.observable (truncation k)).expectation x := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  have hexp (q : Q) : (D.observable q).expectation x =
      ∑' n, fockForm (D.value q) (D.slice (v n)) := by
    rw [← hv.tsum_eq, (D.observable q).expectation_tsum hv.summable
      (fun n => hpositive (A.rankOne_positive (v n)))]
    exact tsum_congr fun n => D.rankOne q (v n)
  have hvalue : D.value radiation = fun u => ⨆ k, D.value (truncation k) u := by
    funext u
    simp_rw [hfull, htruncation, radiationPartial_iSup]
  have hmono (u : h) : Monotone (fun k => D.value (truncation k) u) := by
    simpa only [htruncation] using radiationPartial_monotone coefficient u
  rw [hexp]
  simp_rw [hvalue, fockForm_iSup _ hmono]
  rw [tsum_iSup_monotone]
  · simp_rw [hexp]
  · intro n k l hkl
    simpa only [one_mul] using fockForm_le (C := 1)
      (fun u => by simpa only [one_mul] using hmono u hkl) (D.slice (v n))

/-- Adding the same electronic form to every radiation rank preserves
the increasing recovery identity. -/
theorem energy_eq_iSup_of_radiation {X : Type*}
    (electronic radiation : X → ℝ≥0∞) (truncated : ℕ → X → ℝ≥0∞)
    (x : X) (hrad : radiation x = ⨆ k, truncated k x) :
    electronic x + radiation x = ⨆ k, electronic x + truncated k x := by
  rw [hrad, ENNReal.add_iSup]

/-- Signed electronic potentials can be retained through the same
monotone limit. The negative part is subtracted after summing the positive
electronic and radiation terms. Physical finite-energy identification
uses finiteness of both electronic parts. -/
theorem signed_energy_eq_iSup_of_radiation {X : Type*}
    (positive negative radiation : X → ℝ≥0∞) (truncated : ℕ → X → ℝ≥0∞)
    (x : X) (hrad : radiation x = ⨆ k, truncated k x) :
    positive x + radiation x - negative x =
      ⨆ k, positive x + truncated k x - negative x := by
  rw [hrad, ENNReal.add_iSup, ENNReal.iSup_sub]

end Normal

end GptLean.PhotonLocalizationFormBounds
