import GptLean.PhotonLocalizationChannel

/-!
Countable sector measurements on normal trace-class states. Resolution
of the identity is required only on Hilbert-space vectors. The normal
spectral theorem and nonnegative Fubini prove all mixed-state sums.
-/

namespace GptLean.PhotonLocalizationChannel

open Filter Topology

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

namespace NormalTraceData

variable {R : Gaussian.RankOneData H T} (N : NormalTraceData R)

include N

/-- A positive bounded observable is nonnegative on every positive normal
operator as soon as this is proved on rank-one vectors. -/
theorem observable_nonneg (A : T →L[ℝ] ℝ)
    (hA : ∀ v, 0 ≤ A (R.rankOne v)) {x : T} (hx : x ∈ R.positive) : 0 ≤ A x := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  exact (tsum_nonneg (fun n => hA (v n))).trans_eq (A.hasSum hv).tsum_eq

/-- Nonnegative pure-state resolution identities extend to all positive
normal states. Both the state series and the measurement series are
justified before they are interchanged. -/
theorem measurement_hasSum {ι : Type*} (A : ι → T →L[ℝ] ℝ) (B : T →L[ℝ] ℝ)
    (hA : ∀ i v, 0 ≤ A i (R.rankOne v))
    (hpure : ∀ v, HasSum (fun i => A i (R.rankOne v)) (B (R.rankOne v)))
    {x : T} (hx : x ∈ R.positive) : HasSum (fun i => A i x) (B x) := by
  obtain ⟨v, hv⟩ := N.positive_decomposition x hx
  have hB : HasSum (fun n => B (R.rankOne (v n))) (B x) := B.hasSum hv
  have hs : Summable (fun p : ℕ × ι => A p.2 (R.rankOne (v p.1))) := by
    apply (summable_prod_of_nonneg (fun p => hA p.2 (v p.1))).mpr
    refine ⟨fun n => (hpure (v n)).summable, ?_⟩
    simpa only [(hpure _).tsum_eq] using hB.summable
  have heA : (fun i => ∑' n, A i (R.rankOne (v n))) = fun i => A i x :=
    funext fun i => ((A i).hasSum hv).tsum_eq
  have heB : (fun n => ∑' i, A i (R.rankOne (v n))) = fun n => B (R.rankOne (v n)) :=
    funext fun n => (hpure (v n)).tsum_eq
  have htotal : (∑' i, ∑' n, A i (R.rankOne (v n))) = B x := by
    rw [hs.tsum_comm, heB, hB.tsum_eq]
  rw [heA] at htotal
  have hsum : Summable (fun i => A i x) := heA ▸ hs.prod_symm.prod
  exact htotal ▸ hsum.hasSum

/-- Every nonnegative weighted sector identity follows from the same
normal extension argument. -/
theorem measurement_weighted {ι : Type*} (A : ι → T →L[ℝ] ℝ) (B : T →L[ℝ] ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hA : ∀ i v, 0 ≤ A i (R.rankOne v))
    (hpure : ∀ v, HasSum (fun i => w i * A i (R.rankOne v)) (B (R.rankOne v)))
    {x : T} (hx : x ∈ R.positive) : HasSum (fun i => w i * A i x) (B x) := by
  apply N.measurement_hasSum (fun i => w i • A i) B
    (fun i v => mul_nonneg (hw i) (hA i v)) hpure hx

end NormalTraceData

/-- Standard pairing of a positive trace-class operator with `C* C`,
uniform in every bounded map into an auxiliary Hilbert space. -/
structure QuadraticTrace {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (R : Gaussian.RankOneData H T) where
  effect : (H →L[ℂ] G) → T →L[ℝ] ℝ
  rankOne : ∀ C v, effect C (R.rankOne v) = ‖C v‖ ^ 2

namespace QuadraticTrace

variable {G ι : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  {R : Gaussian.RankOneData H T} (Q : QuadraticTrace (G := G) R)

/-- A joint sector mass is explicitly the trace of its squared projection
coordinate, not an assumed probability distribution. -/
noncomputable def sectorEffect (J : H →ₗᵢ[ℂ] lp (fun _ : ι => G) 2)
    (i : ι) : T →L[ℝ] ℝ :=
  Q.effect ((lp.evalCLM ℂ (fun _ : ι => G) 2 i).comp J.toContinuousLinearMap)

@[simp] theorem sectorEffect_rankOne (J : H →ₗᵢ[ℂ] lp (fun _ : ι => G) 2)
    (i : ι) (v : H) : Q.sectorEffect J i (R.rankOne v) = ‖J v i‖ ^ 2 :=
  Q.rankOne _ _

/-- The pure joint-sector resolution is Parseval, with no sector-tail
estimate or finite number expectation needed. -/
theorem sectorEffect_pure_hasSum (J : H →ₗᵢ[ℂ] lp (fun _ : ι => G) 2) (v : H) :
    HasSum (fun i => Q.sectorEffect J i (R.rankOne v)) (R.trace (R.rankOne v)) := by
  simp only [Q.sectorEffect_rankOne, R.trace_rankOne]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, J.norm_map] using
    lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (J v)

theorem sectorEffect_nonneg (N : NormalTraceData R)
    (J : H →ₗᵢ[ℂ] lp (fun _ : ι => G) 2) (i : ι) {x : T} (hx : x ∈ R.positive) :
    0 ≤ Q.sectorEffect J i x :=
  N.observable_nonneg _ (fun v => by rw [Q.sectorEffect_rankOne]; positivity) hx

/-- The physical joint sector probabilities of a mixed state are
summable and have total mass equal to its trace. -/
theorem sectorEffect_hasSum (N : NormalTraceData R)
    (J : H →ₗᵢ[ℂ] lp (fun _ : ι => G) 2) {x : T} (hx : x ∈ R.positive) :
    HasSum (fun i => Q.sectorEffect J i x) (R.trace x) :=
  N.measurement_hasSum _ R.trace
    (fun i v => by rw [Q.sectorEffect_rankOne]; positivity)
    (Q.sectorEffect_pure_hasSum J) hx

end QuadraticTrace

end GptLean.PhotonLocalizationChannel
