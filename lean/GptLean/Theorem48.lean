import GptLean.Closure
import GptLean.AttainmentConstruction
import GptLean.PhotonLossClosure
import GptLean.InfraredRepair
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
The functional conclusions of `thm-unrestricted-attainment`.

The Lieb functional is defined from pure-state potential energies in the
article. Its identification therefore uses spectral decomposition of mixed
states, rather than the later soft-purification theorem. The elementary
averaging argument below derives equality of the potential infima from
countable spectral ensembles. This is permitted operator-theoretic background
and does not assume equality of either constrained search.

The final theorem derives attainment, the uniform photon-number estimate,
norm lower semicontinuity and identification with the pure-state Lieb
functional. The exact removal and retained-state compactness interfaces are
explicit unresolved physical inputs. They are not part of the permitted
convex-analysis or operator background.
-/

namespace GptLean.Theorem48

open Filter Topology
open scoped ENNReal

variable {P M D V : Type*}

/-- A normalized countable spectral ensemble for one mixed state and one
external potential. The weighted energy identity is ordinary spectral and
trace calculus. No constraint-preserving pure recovery is required. -/
structure SpectralEnsemble (A : DFT.StateModel P D) (B : DFT.StateModel M D)
    (pair : V → D → ℝ) (m : M) (v : V) where
  pure : ℕ → P
  weight : ℕ → ℝ
  weight_nonneg : ∀ n, 0 ≤ weight n
  weight_summable : Summable weight
  weight_sum : ∑' n, weight n = 1
  energy_summable : Summable fun n =>
    weight n * (A.energy (pure n) + pair v (A.density (pure n)))
  energy_sum : (∑' n, weight n *
    (A.energy (pure n) + pair v (A.density (pure n)))) =
      B.energy m + pair v (B.density m)

/-- Every normalized summable average has a term below any strict upper
bound of its average. This also permits zero spectral weights. -/
theorem exists_term_lt_average_add
    (value weight : ℕ → ℝ) (hw : ∀ n, 0 ≤ weight n)
    (hs : Summable weight) (hunit : ∑' n, weight n = 1)
    (hvalue : Summable fun n => weight n * value n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n, value n < (∑' j, weight j * value j) + ε := by
  by_contra hn
  push Not at hn
  set average := ∑' j, weight j * value j
  have hle : average + ε ≤ average := by
    calc
      average + ε = (∑' n, weight n) * (average + ε) := by rw [hunit, one_mul]
      _ = ∑' n, weight n * (average + ε) := (hs.tsum_mul_right _).symm
      _ ≤ ∑' n, weight n * value n :=
        Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hn n) (hw n))
          (hs.mul_right _) hvalue
      _ = average := rfl
  linarith

/-- Spectral averaging supplies an approximate pure-state variational
competitor. It does not preserve the mixed state's density/current pair. -/
theorem spectral_approximation (A : DFT.StateModel P D) (B : DFT.StateModel M D)
    (pair : V → D → ℝ) (m : M) (v : V)
    (S : SpectralEnsemble A B pair m v) {ε : ℝ} (hε : 0 < ε) :
    ∃ p, A.energy p + pair v (A.density p) <
      B.energy m + pair v (B.density m) + ε := by
  obtain ⟨n, hn⟩ := exists_term_lt_average_add
    (fun n => A.energy (S.pure n) + pair v (A.density (S.pure n)))
    S.weight S.weight_nonneg S.weight_summable S.weight_sum S.energy_summable hε
  rw [S.energy_sum] at hn
  exact ⟨S.pure n, hn⟩

/-- Pure and mixed potential energies agree by spectral decomposition and
the rank-one inclusion. The constrained-search equality is not a premise. -/
theorem ground_eq_of_spectral_ensembles
    (A : DFT.StateModel P D) (B : DFT.StateModel M D)
    (emb : DFT.PureEmbedding A B) (pair : V → D → ℝ)
    (spectral : ∀ m v, Nonempty (SpectralEnsemble A B pair m v)) (v : V) :
    DFT.ground A pair v = DFT.ground B pair v := by
  apply le_antisymm
  · refine le_iInf fun m => DFT.ereal_le_of_epsilon fun ε hε => ?_
    obtain ⟨S⟩ := spectral m v
    obtain ⟨p, hp⟩ := spectral_approximation A B pair m v S hε
    exact (iInf_le _ p).trans (EReal.coe_le_coe hp.le)
  · refine le_iInf fun p => ?_
    have h := iInf_le
      (fun m => ((B.energy m + pair v (B.density m) : ℝ) : EReal)) (emb.toMixed p)
    simpa only [DFT.ground, emb.energy_eq, emb.density_eq] using h

/-- The Lieb functionals are equal even before establishing equality of
the constrained searches or any exact-density pure approximation. -/
theorem lieb_eq_of_spectral_ensembles
    (A : DFT.StateModel P D) (B : DFT.StateModel M D)
    (emb : DFT.PureEmbedding A B) (pair : V → D → ℝ)
    (spectral : ∀ m v, Nonempty (SpectralEnsemble A B pair m v)) (d : D) :
    DFT.lieb A pair d = DFT.lieb B pair d := by
  simp only [DFT.lieb, ground_eq_of_spectral_ensembles A B emb pair spectral]

/-- All conclusions of Theorem 4.8, conditional on the stated exact repair
and photon-loss interfaces. Neither attainment, a photon-number estimate,
lower semicontinuity nor a functional equality is assumed.

The topology here is specifically the norm topology of the density/current
space. The quantitative estimate holds for every optimizer. The constant is
determined by the fixed infrared repair data and is independent of the pair.
-/
theorem all_conclusions_of_closure
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    {Ω : Type*} [MeasurableSpace Ω]
    (A : DFT.StateModel P D) (B : DFT.StateModel M D)
    (number : M → ℝ≥0∞) (μ : MeasureTheory.Measure Ω) [MeasureTheory.SFinite μ]
    (ω : Ω → ℝ) (w : Ω → ℝ≥0∞)
    (I : AttainmentConstruction.InfraredRepairData B number μ ω w)
    (hpositive : ∀ m, 0 ≤ B.energy m)
    (hloss : ∀ d, Attainment.PhotonLossInput M (fun m => B.density m = d)
      B.energy number)
    (hclosed : Closure.BoundedConstraintClosure B number)
    (m₀ : M) (hmix : DFT.MixtureClosed B)
    (emb : DFT.PureEmbedding A B) (pair : V → D → ℝ)
    (spectral : ∀ m v, Nonempty (SpectralEnsemble A B pair m v))
    (fm : DFT.FenchelMoreau pair) :
    (∀ d, DFT.search B d < ⊤ → ∃ m,
      B.density m = d ∧ (B.energy m : EReal) = DFT.search B d ∧
        number m ≤ ENNReal.ofReal (I.numberConstant * (1 + B.energy m))) ∧
    (∀ m, (B.energy m : EReal) = DFT.search B (B.density m) →
      number m ≤ ENNReal.ofReal (I.numberConstant * (1 + B.energy m))) ∧
    LowerSemicontinuous (DFT.search B) ∧
    (∀ d, DFT.search B d = DFT.lieb A pair d) := by
  have hminimizer := I.attainment hpositive hloss
  have hlsc := Closure.search_lowerSemicontinuous B number I.numberConstant
    I.numberConstant_nonneg hpositive hminimizer hclosed
  refine ⟨hminimizer, fun _ he => I.optimizer_number_bound hpositive he, hlsc, ?_⟩
  intro d
  exact (DFT.mixed_eq_lieb B pair fm 0 hpositive m₀
    (DFT.mixed_search_convex B hmix) hlsc d).trans
      (lieb_eq_of_spectral_ensembles A B emb pair spectral d).symm

/-- The complete theorem assembly from exact infrared repair, explicit
localization estimates and a realization of the physical constraints.
The fixed-fiber and varying-pair compactness statements are proved by
`PhotonLossClosure`, so neither appears as a premise here.

The remaining PF obligations are the construction of the repair output,
the concrete localization data and estimates, and their trace-space
realization. Standard trace calculus, spectral ensembles, mixing and
Fenchel–Moreau remain separately identified background inputs.
-/
theorem all_conclusions
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    {Ω X Test : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [CompleteSpace X]
    (A : DFT.StateModel P D) (B : DFT.StateModel M D)
    (number : M → ℝ≥0∞) (μ : MeasureTheory.Measure Ω) [MeasureTheory.SFinite μ]
    (ω : Ω → ℝ) (w : Ω → ℝ≥0∞)
    (I : AttainmentConstruction.InfraredRepairData B number μ ω w)
    (L : PhotonLoss.LocalizationData X) (T : PhotonLoss.TraceData L Test)
    (J : PhotonLoss.LocalizationEstimates L T)
    (R : PhotonLoss.ConstraintRealization J B number)
    (m₀ : M) (hmix : DFT.MixtureClosed B)
    (emb : DFT.PureEmbedding A B) (pair : V → D → ℝ)
    (spectral : ∀ m v, Nonempty (SpectralEnsemble A B pair m v))
    (fm : DFT.FenchelMoreau pair) :
    (∀ d, DFT.search B d < ⊤ → ∃ m,
      B.density m = d ∧ (B.energy m : EReal) = DFT.search B d ∧
        number m ≤ ENNReal.ofReal (I.numberConstant * (1 + B.energy m)) ∧
        number m < ⊤) ∧
    (∀ m, (B.energy m : EReal) = DFT.search B (B.density m) →
      number m ≤ ENNReal.ofReal (I.numberConstant * (1 + B.energy m))) ∧
    LowerSemicontinuous (DFT.search B) ∧
    (∀ d, DFT.search B d = DFT.lieb A pair d) := by
  obtain ⟨hatt, hnumber, hlsc, heq⟩ := all_conclusions_of_closure A B number μ ω w I
    R.energy_nonneg R.photonLossInput R.boundedConstraintClosure m₀ hmix emb pair
    spectral fm
  refine ⟨?_, hnumber, hlsc, heq⟩
  intro d hd
  obtain ⟨m, hm, he, hn⟩ := hatt d hd
  exact ⟨m, hm, he, hn, hn.trans_lt ENNReal.ofReal_lt_top⟩

/-- All conclusions from the localized repaired-cluster output. The proof
chooses the infrared scale, sums and optimizes the local repair costs,
absorbs the soft energy, and derives both compactness interfaces.

Thus the number constant is produced before the constraint pair. The local
physical state construction and localization estimates are still explicit
premises, rather than being reclassified as standard background.
-/
theorem all_conclusions_of_localized_removal
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    {Ω X Test PhotonMarginal : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [CompleteSpace X]
    (A : DFT.StateModel P D) (B : DFT.StateModel M D)
    (number : M → ℝ≥0∞) (μ : MeasureTheory.Measure Ω) [MeasureTheory.SFinite μ]
    (ω : Ω → ℝ) (w : Ω → ℝ≥0∞)
    (F : InfraredRepair.InfraredMoments B number μ ω w)
    (marginal : ℝ → M → PhotonMarginal) (target : M → ℝ → PhotonMarginal)
    {C e : ℝ} (hC : 0 ≤ C) (he : 0 ≤ e)
    (hlocal : ∀ m κ R, 0 < κ → κ ≤ 1 → 1 ≤ R → κ * R ≤ 1 →
      SoftRemoval.LocalizedOutput B m (marginal κ) (target m κ) (F.softEnergy m κ)
        C e κ R (Real.sqrt (CutoffProfile.asq μ ω w κ))
          (Real.sqrt (CutoffProfile.bsq μ ω w κ)))
    (hmarginal : ∀ m κ r, 0 < κ → marginal κ r = target m κ →
      number r ≤ ENNReal.ofReal (F.hardNumber m κ))
    (L : PhotonLoss.LocalizationData X) (T : PhotonLoss.TraceData L Test)
    (J : PhotonLoss.LocalizationEstimates L T)
    (R : PhotonLoss.ConstraintRealization J B number)
    (m₀ : M) (hmix : DFT.MixtureClosed B)
    (emb : DFT.PureEmbedding A B) (pair : V → D → ℝ)
    (spectral : ∀ m v, Nonempty (SpectralEnsemble A B pair m v))
    (fm : DFT.FenchelMoreau pair) :
    ∃ Cnumber : ℝ, 0 ≤ Cnumber ∧
      (∀ d, DFT.search B d < ⊤ → ∃ m,
        B.density m = d ∧ (B.energy m : EReal) = DFT.search B d ∧
          number m ≤ ENNReal.ofReal (Cnumber * (1 + B.energy m)) ∧
          number m < ⊤) ∧
      (∀ m, (B.energy m : EReal) = DFT.search B (B.density m) →
        number m ≤ ENNReal.ofReal (Cnumber * (1 + B.energy m))) ∧
      LowerSemicontinuous (DFT.search B) ∧
      (∀ d, DFT.search B d = DFT.lieb A pair d) := by
  obtain ⟨I⟩ := InfraredRepair.exists_data_of_localized F marginal target hC he
    hlocal hmarginal
  exact ⟨I.numberConstant, I.numberConstant_nonneg,
    all_conclusions A B number μ ω w I L T J R m₀ hmix emb pair spectral fm⟩

end GptLean.Theorem48
