import GptLean.PhysicalFockFormCalculus
import GptLean.PhysicalFockChannel

/-!
The concrete Fock form calculus with electronic L2 and a one-photon
unitary included. The electronic slices are obtained from the actual
scalar spatial Hilbert basis. Normal partial trace supplies their form
observables, and bounded fiber operators commute with those coefficients.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel PhotonLocalizationFockChannel
  PhotonLocalizationFormBounds PhysicalNormalTrace PhysicalNormalTrace.StandardNormalTraceBackground
  PhysicalL2HilbertSum RemovalState
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

section PartialTraceForm
variable (BT : StandardNormalTraceBackground)
  {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def partialTraceForm (W : H →ₗᵢ[ℂ] lp (fun _ : ℕ => K) 2)
    (E : PositiveForm (BT.traceData (H := K))) : PositiveForm (BT.traceData (H := H)) where
  truncation n := (E.truncation n).comp (BT.partialTrace W)
  nonneg n _x hx := E.nonneg n _ (BT.partialTrace_positive W hx)
  monotone _x hx := E.monotone _ (BT.partialTrace_positive W hx)

theorem partialTraceForm_rankOne (W : H →ₗᵢ[ℂ] lp (fun _ : ℕ => K) 2)
    (E : PositiveForm (BT.traceData (H := K))) (u : H) :
    (partialTraceForm BT W E).expectation ((BT.realization H).rank.rankOne u) =
      ∑' a, E.expectation ((BT.realization K).rank.rankOne (W u a)) := by
  change E.expectation (BT.partialTrace W ((BT.realization H).rank.rankOne u)) = _
  rw [BT.partialTrace_rankOne]
  exact E.expectation_tsum
    (Repair.rankOneSeries_hasSum (BT.realization K).rank
      (StandardNormalTraceBackground.dilation_mass W u)).summable
    (fun a => (BT.realization K).rank.rankOne_positive (W u a))

end PartialTraceForm

private theorem fockForm_flatten {h : Type*} (q : h → ℝ≥0∞)
    (s : ℕ → (m : ℕ) → Fin m → ℕ → h) :
    fockForm q (fun m i a => s a.unpair.1 m i a.unpair.2) =
      ∑' b, fockForm q (s b) := by
  unfold fockForm sectorForm
  simp_rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  have he (m : ℕ) (i : Fin m) :
      (∑' a : ℕ, q (s a.unpair.1 m i a.unpair.2)) = ∑' b, ∑' a, q (s b m i a) :=
    (Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ => q (s p.1 m i p.2))).trans ENNReal.tsum_prod'
  calc
    _ = ∑' m, ∑' i : Fin m, ∑' b, ∑' a, q (s b m i a) :=
      tsum_congr (fun m => tsum_congr (he m))
    _ = ∑' m, ∑' b, ∑' i : Fin m, ∑' a, q (s b m i a) :=
      tsum_congr (fun _ => ENNReal.tsum_comm)
    _ = _ := ENNReal.tsum_comm

section Electronic
variable {X h H : Type} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]
  [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (BT : StandardNormalTraceBackground) {Q : Type}
  (F : FockFactorization h H)
  (D : FockFormCalculus (BT.realization H).rank (BT.traceData (H := H)) F Q)

def electronicFormSlices (u : Lp H 2 μ) (m : ℕ) (i : Fin m) (a : ℕ) : h :=
  D.slice (spatialCoefficients μ H u a.unpair.1) m i a.unpair.2

def electronicFormObservable (q : Q) : PositiveForm (BT.traceData (H := Lp H 2 μ)) :=
  partialTraceForm BT (spatialCoefficients μ H) (D.observable q)

theorem electronicFormObservable_slices (q : Q) (u : Lp H 2 μ) :
    (electronicFormObservable μ BT F D q).expectation ((BT.realization (Lp H 2 μ)).rank.rankOne u) =
      fockForm (D.value q) (electronicFormSlices μ BT F D u) :=
  (partialTraceForm_rankOne BT (spatialCoefficients μ H) (D.observable q) u).trans
    ((tsum_congr (fun b => D.rankOne q (spatialCoefficients μ H u b))).trans
      (fockForm_flatten (D.value q) (fun b => D.slice (spatialCoefficients μ H u b))).symm)

theorem electronicFactorization_coefficients
    (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (u : Lp H 2 μ) (a b : ℕ) :
    spatialCoefficients μ H ((electronicFactorization μ F).factor j u a) b =
      F.factor j (spatialCoefficients μ H u b) a :=
  spatialCoefficients_compLpL μ H
    ((lp.evalCLM ℂ (fun _ : ℕ => H) 2 a).comp (F.factor j).toContinuousLinearMap) u b

theorem electronicFormObservable_pullback
    (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (q : Q) (u : Lp H 2 μ) :
    (∑' a, (electronicFormObservable μ BT F D q).expectation
      ((BT.realization (Lp H 2 μ)).rank.rankOne ((electronicFactorization μ F).factor j u a))) =
      fockForm (fun v => D.value q (retainedMap j v)) (electronicFormSlices μ BT F D u) := by
  calc
    _ = ∑' a, ∑' b, (D.observable q).expectation ((BT.realization H).rank.rankOne
        (spatialCoefficients μ H ((electronicFactorization μ F).factor j u a) b)) :=
      tsum_congr (fun a => partialTraceForm_rankOne BT (spatialCoefficients μ H) (D.observable q) _)
    _ = ∑' b, ∑' a, (D.observable q).expectation ((BT.realization H).rank.rankOne
        (F.factor j (spatialCoefficients μ H u b) a)) := by
      rw [ENNReal.tsum_comm]
      exact tsum_congr (fun b => tsum_congr (fun a =>
        congrArg (fun w => (D.observable q).expectation ((BT.realization H).rank.rankOne w))
          (electronicFactorization_coefficients μ F j u a b)))
    _ = ∑' b, fockForm (fun v => D.value q (retainedMap j v))
        (D.slice (spatialCoefficients μ H u b)) := tsum_congr (fun b => D.pullback j q _)
    _ = _ := (fockForm_flatten (fun v => D.value q (retainedMap j v))
      (fun b => D.slice (spatialCoefficients μ H u b))).symm

def electronicFormCalculus : FockFormCalculus (BT.realization (Lp H 2 μ)).rank
    (BT.traceData (H := Lp H 2 μ)) (electronicFactorization μ F) Q where
  value := D.value
  observable := electronicFormObservable μ BT F D
  slice := electronicFormSlices μ BT F D
  rankOne := electronicFormObservable_slices μ BT F D
  pullback := electronicFormObservable_pullback μ BT F D

end Electronic

section Transport
variable {h k H T Q : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup k] [InnerProductSpace ℂ k]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T} {Tr : PositiveTraceData T}
  (e : h ≃ₗᵢ[ℂ] k) {F : FockFactorization k H} (D : FockFormCalculus R Tr F Q)

def transportFormCalculus : FockFormCalculus R Tr (transportFactorization e F) Q where
  value q u := D.value q (e u)
  observable := D.observable
  slice v m i a := e.symm (D.slice v m i a)
  rankOne q v := by
    simpa only [fockForm, sectorForm, e.apply_symm_apply] using D.rankOne q v
  pullback j q v := by
    have h := D.pullback (transportSplit e j) q v
    simpa only [transportFactorization, fockForm, sectorForm, transportSplit_retained] using h

end Transport

/-- The same physical full factorization now carries its constructed form calculus. -/
def fullFormCalculus (BF : StandardSymmetricFockExponential)
    (CCR : CanonicalSectorCCR photonMeasure) (BT : StandardNormalTraceBackground)
    {h : Type} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
    (e : h ≃ₗᵢ[ℂ] Lp ℂ 2 photonMeasure) (N : ℕ) :
    FockFormCalculus (BT.realization (FullHilbert N)).rank (BT.traceData (H := FullHilbert N))
      (fullFactorization BF e N) OnePhotonFormFamily :=
  electronicFormCalculus (volume : Measure (SymmetricLift.Configuration N)) BT
    (transportFactorization e (photonFactorization BF))
    (transportFormCalculus e (photonFormCalculus BT.normal (BT.realization PhotonFock).functional BF CCR))

end GptLean.PhysicalFock
