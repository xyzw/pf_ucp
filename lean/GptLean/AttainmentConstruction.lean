import GptLean.Attainment
import GptLean.DFT
import GptLean.HardLayerCake

/-!
The construction step in `thm-unrestricted-attainment`.

The constrained-search infimum itself supplies epsilon competitors and an
exact-constraint minimizing sequence. A cutoff repair is then selected on
an admissible tail and compactness is applied to its number-bounded output.
Photon moments are genuine Lebesgue integrals, so the optimizer estimate
controls a full moment which was allowed to be infinite.

`InfraredRepairData.repair` and `Attainment.PhotonLossInput` are explicit
Pauli–Fierz analytic inputs. They are not asserted as general operator
background, nor does this module construct physical density matrices.
-/

namespace GptLean.AttainmentConstruction

open Filter Topology MeasureTheory Set
open scoped ENNReal

variable {State Pair : Type*}

/-- Every positive tolerance admits an exact-constraint competitor. -/
theorem exists_near_minimizer (A : DFT.StateModel State Pair) (d : Pair) {F ε : ℝ}
    (hF : DFT.search A d = (F : EReal)) (hε : 0 < ε) :
    ∃ s, A.density s = d ∧ A.energy s < F + ε := by
  by_contra h
  push Not at h
  have hf : ((F + ε : ℝ) : EReal) ≤ DFT.search A d :=
    le_iInf₂ fun s hs => EReal.coe_le_coe (h s hs)
  rw [hF] at hf
  have := EReal.coe_le_coe_iff.mp hf
  linarith

/-- No minimizing sequence is assumed. It is selected from the `EReal`
infimum, with a concrete error tending to zero. -/
theorem exists_minimizing_sequence (A : DFT.StateModel State Pair) (d : Pair) {F : ℝ}
    (hF : DFT.search A d = (F : EReal)) :
    ∃ s : ℕ → State, (∀ n, A.density (s n) = d) ∧
      (∀ n, F ≤ A.energy (s n)) ∧
      (∀ n, A.energy (s n) < F + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n => A.energy (s n)) atTop (𝓝 F) := by
  have hex (n : ℕ) := exists_near_minimizer A d hF
    (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  choose s hs he using hex
  have hl (n : ℕ) : F ≤ A.energy (s n) := by
    have h := DFT.search_le A (hs n)
    rw [hF] at h
    exact EReal.coe_le_coe_iff.mp h
  refine ⟨s, hs, hl, he, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add F)
    hl (fun n => (he n).le)

/-- A general direct-method lemma with a scale-dependent exact repair.
The minimizing sequence, admissible cutoff tail and uniform bounds are
constructed within the proof. -/
theorem attainment_of_cutoff_repair
    (A : DFT.StateModel State Pair) (number : State → ℝ≥0∞) (d : Pair)
    {F κ₀ C : ℝ} {err : ℝ → ℝ}
    (hF : DFT.search A d = (F : EReal)) (hκ₀ : 0 < κ₀)
    (herr : Tendsto err (𝓝[>] 0) (𝓝 0))
    (hrepair : ∀ s, A.density s = d → ∀ κ, 0 < κ → κ < κ₀ →
      ∃ r, A.density r = d ∧ A.energy r ≤ A.energy s + err κ ∧
        number r ≤ ENNReal.ofReal (A.energy s / κ₀ +
          2 * ((A.energy s - F) / κ) + C))
    (hloss : Attainment.PhotonLossInput State (fun s => A.density s = d)
      A.energy number) :
    ∃ s, A.density s = d ∧ A.energy s = F ∧ number s < ⊤ := by
  obtain ⟨s, hs, hl, _, hlim⟩ := exists_minimizing_sequence A d hF
  let excess : ℕ → ℝ := fun n => A.energy (s n) - F
  have hd : ∀ n, 0 ≤ excess n := fun n => sub_nonneg.mpr (hl n)
  have hdlim : Tendsto excess atTop (𝓝 0) := by
    simpa [excess] using hlim.sub_const F
  obtain ⟨n₀, hn₀⟩ := Attainment.cutoff_small_on_tail hdlim hκ₀
  let k : ℕ → ℝ := fun n => Attainment.cutoff excess (n + n₀)
  have hklim : Tendsto k atTop (𝓝 0) :=
    (Attainment.cutoff_tendsto_zero hdlim).comp (tendsto_add_atTop_nat n₀)
  have hkright : Tendsto k atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hklim, Eventually.of_forall (fun n => (hn₀ n).1)⟩
  have hslim : Tendsto (fun n => A.energy (s (n + n₀))) atTop (𝓝 F) :=
    hlim.comp (tendsto_add_atTop_nat n₀)
  have hratio : Tendsto (fun n => excess (n + n₀) / k n) atTop (𝓝 0) :=
    (Attainment.excess_div_cutoff_tendsto_zero hd hdlim).comp
      (tendsto_add_atTop_nat n₀)
  have hr (n : ℕ) := hrepair (s (n + n₀)) (hs _) (k n) (hn₀ n).1 (hn₀ n).2
  choose r hrpair hrenergy hrnumber using hr
  have hfloor (t : State) (ht : A.density t = d) : F ≤ A.energy t := by
    have h := DFT.search_le A ht
    rw [hF] at h
    exact EReal.coe_le_coe_iff.mp h
  have hrlim := Attainment.repaired_energy_tendsto hslim (herr.comp hkright)
    (fun n => hfloor _ (hrpair n)) hrenergy
  have hcap : Tendsto (fun n => A.energy (s (n + n₀)) / κ₀ +
      2 * ((A.energy (s (n + n₀)) - F) / k n) + C)
      atTop (𝓝 (F / κ₀ + C)) := by
    simpa [excess] using ((hslim.div_const κ₀).add (hratio.const_mul 2)).add_const C
  obtain ⟨M, hM⟩ := hcap.bddAbove_range
  obtain ⟨E, hE⟩ := hrlim.bddAbove_range
  obtain ⟨r₀, hr₀, he₀, hn₀⟩ := hloss r F M hrpair
    ⟨E, fun n => hE (Set.mem_range_self n)⟩
    (fun n => (hrnumber n).trans (ENNReal.ofReal_le_ofReal (hM (Set.mem_range_self n))))
    hrlim
  exact ⟨r₀, hr₀, le_antisymm he₀ (hfloor _ hr₀), hn₀.trans_lt ENNReal.ofReal_lt_top⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Explicit moment identities and the same-output repair gain/marginal
estimate. The repair field is a paper-specific analytic premise. -/
structure InfraredRepairData (A : DFT.StateModel State Pair)
    (number : State → ℝ≥0∞) (μ : Measure Ω) (ω : Ω → ℝ) (w : Ω → ℝ≥0∞) where
  κ₀ : ℝ
  C : ℝ
  κ₀_pos : 0 < κ₀
  C_nonneg : 0 ≤ C
  dispersion_measurable : Measurable ω
  dispersion_positive : ∀ᵐ x ∂μ, 0 < ω x
  cutoff_measurable : Measurable w
  cutoff_finite : ∫⁻ x, w x ∂μ < ⊤
  weighted_finite : ∫⁻ x, w x * ENNReal.ofReal (1 / ω x) ∂μ < ⊤
  photonDensity : State → Ω → ℝ≥0∞
  hardNumber : State → ℝ → ℝ
  softEnergy : State → ℝ → ℝ
  radiationEnergy : State → ℝ
  moments : ∀ s, HardLayerCake.HasPhotonDensity μ ω (photonDensity s)
    (hardNumber s) (softEnergy s) (radiationEnergy s)
  radiation_le : ∀ s, radiationEnergy s ≤ A.energy s
  number_eq : ∀ s, number s = ∫⁻ x, photonDensity s x ∂μ
  repair : ∀ s κ, 0 < κ → κ ≤ κ₀ → ∃ r,
    A.density r = A.density s ∧
    A.energy r ≤ A.energy s - softEnergy s κ / 2 +
      C * (κ ^ 2 + CutoffProfile.bsq μ ω w κ) ∧
    number r ≤ ENNReal.ofReal (hardNumber s κ)

namespace InfraredRepairData

variable {A : DFT.StateModel State Pair} {number : State → ℝ≥0∞}
  {μ : Measure Ω} {ω : Ω → ℝ} {w : Ω → ℝ≥0∞}
  (I : InfraredRepairData A number μ ω w)

noncomputable def numberConstant : ℝ :=
  max (1 / I.κ₀) ((2 * I.C) * (I.κ₀ + CutoffProfile.asq μ ω w I.κ₀))

theorem numberConstant_nonneg : 0 ≤ I.numberConstant := by
  have hk := I.κ₀_pos
  exact (by positivity : (0 : ℝ) ≤ 1 / I.κ₀).trans (le_max_left _ _)

/-- Compare the repaired feasible competitor to the actual search value. -/
theorem soft_bound {d : Pair} {F : ℝ} (hF : DFT.search A d = (F : EReal))
    {s : State} (hs : A.density s = d) {κ : ℝ} (hκ : 0 < κ) (hκ₀ : κ ≤ I.κ₀) :
    I.softEnergy s κ ≤ 2 * (A.energy s - F) +
      (2 * I.C) * (κ ^ 2 + CutoffProfile.bsq μ ω w κ) := by
  obtain ⟨r, hr, he, _⟩ := I.repair s κ hκ hκ₀
  have hfloor := DFT.search_le A (hr.trans hs)
  rw [hF] at hfloor
  have hfloor' := EReal.coe_le_coe_iff.mp hfloor
  linarith

variable [SFinite μ]

/-- The hard-number bound uses Tonelli and the actual infrared profile. -/
theorem hard_number_bound {d : Pair} {F : ℝ} (hF : DFT.search A d = (F : EReal))
    {s : State} (hs : A.density s = d) {κ : ℝ} (hκ : 0 < κ) (hκ₀ : κ < I.κ₀) :
    I.hardNumber s κ ≤ A.energy s / I.κ₀ + 2 * (A.energy s - F) / κ +
      (2 * I.C) * (I.κ₀ + CutoffProfile.asq μ ω w I.κ₀) := by
  have hC0 := I.C_nonneg
  have hfloor := DFT.search_le A hs
  rw [hF] at hfloor
  exact HardLayerCake.numHard_le_of_infrared_profile μ I.dispersion_measurable
    I.dispersion_positive (I.moments s) (I.radiation_le s) I.cutoff_measurable
    I.cutoff_finite I.weighted_finite hκ hκ₀
    (sub_nonneg.mpr (EReal.coe_le_coe_iff.mp hfloor)) (by positivity)
    (fun t ht => I.soft_bound hF hs (hκ.trans ht.1) ht.2)

/-- Full photon-number control for every optimizer. The full number may
initially be infinite. No number bound on that optimizer is a premise. -/
theorem optimizer_number_bound (hpositive : ∀ s, 0 ≤ A.energy s)
    {s : State} (he : (A.energy s : EReal) = DFT.search A (A.density s)) :
    number s ≤ ENNReal.ofReal (I.numberConstant * (1 + A.energy s)) := by
  have hC0 := I.C_nonneg
  have hk0 := I.κ₀_pos
  have hE0 := hpositive s
  have hC : 0 ≤ 2 * I.C := by positivity
  have hA0 := CutoffProfile.asq_nonneg (μ := μ) (ω := ω) (w := w) I.κ₀
  have hsoftfin (t : ℝ) :
      (∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * I.photonDensity s x ∂μ) ≠ ⊤ :=
    (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) (I.moments s).finite).ne
  have hcutfin (t : ℝ) : (∫⁻ x in {x | ω x < t}, w x ∂μ) ≠ ⊤ :=
    (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) I.cutoff_finite).ne
  have hweighted :
      (∫⁻ x in {x | ω x < I.κ₀}, w x * ENNReal.ofReal (1 / ω x) ∂μ) ≠ ⊤ :=
    (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) I.weighted_finite).ne
  have hq (t : ℝ) (ht : t ∈ Ioc 0 I.κ₀) :
      ∫⁻ x in {x | ω x < t}, ENNReal.ofReal (ω x) * I.photonDensity s x ∂μ
        ≤ ENNReal.ofReal (2 * I.C) *
          (ENNReal.ofReal (t ^ 2) + ∫⁻ x in {x | ω x < t}, w x ∂μ) := by
    have hb := I.soft_bound he.symm rfl ht.1 ht.2
    simp only [sub_self, mul_zero, zero_add] at hb
    have hen := ENNReal.ofReal_le_ofReal hb
    rw [(I.moments s).Esoft_eq, ENNReal.ofReal_toReal (hsoftfin t)] at hen
    rw [ENNReal.ofReal_mul hC,
      ENNReal.ofReal_add (sq_nonneg t) (CutoffProfile.bsq_nonneg t),
      CutoffProfile.bsq, ENNReal.ofReal_toReal (hcutfin t)] at hen
    exact hen
  have hrad : (∫⁻ x, ENNReal.ofReal (ω x) * I.photonDensity s x ∂μ)
      ≤ ENNReal.ofReal (A.energy s) := by
    rw [← ENNReal.ofReal_toReal (I.moments s).finite.ne, ← (I.moments s).Erad_eq]
    exact ENNReal.ofReal_le_ofReal (I.radiation_le s)
  have hbound := LayerCake.photon_number_le μ I.dispersion_measurable
    I.dispersion_positive (I.moments s).measurable I.cutoff_measurable I.κ₀_pos hq
  have hweighted_eq :
      ∫⁻ x in {x | ω x < I.κ₀}, w x * ENNReal.ofReal (1 / ω x) ∂μ
        = ENNReal.ofReal (CutoffProfile.asq μ ω w I.κ₀) := by
    exact (ENNReal.ofReal_toReal hweighted).symm
  have hnum : number s ≤ ENNReal.ofReal
      (A.energy s / I.κ₀ + (2 * I.C) * (I.κ₀ + CutoffProfile.asq μ ω w I.κ₀)) := by
    rw [I.number_eq]
    refine hbound.trans ?_
    rw [hweighted_eq]
    calc
      _ ≤ ENNReal.ofReal (1 / I.κ₀) * ENNReal.ofReal (A.energy s) +
          (ENNReal.ofReal (2 * I.C) * ENNReal.ofReal I.κ₀ +
            ENNReal.ofReal (2 * I.C) * ENNReal.ofReal (CutoffProfile.asq μ ω w I.κ₀)) :=
        add_le_add (mul_le_mul' le_rfl hrad) le_rfl
      _ = _ := by
        rw [← mul_add, ← ENNReal.ofReal_add I.κ₀_pos.le hA0,
          ← ENNReal.ofReal_mul hC,
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / I.κ₀),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  exact hnum.trans (ENNReal.ofReal_le_ofReal
    (LayerCake.uniform_number_bound (hpositive s) le_rfl))

/-- Attainment for the actual extended-real search with the uniform
number estimate required by the lower-semicontinuity argument. -/
theorem attainment (hpositive : ∀ s, 0 ≤ A.energy s)
    (hloss : ∀ d, Attainment.PhotonLossInput State (fun s => A.density s = d)
      A.energy number) (d : Pair) (hfinite : DFT.search A d < ⊤) :
    ∃ s, A.density s = d ∧ (A.energy s : EReal) = DFT.search A d ∧
      number s ≤ ENNReal.ofReal (I.numberConstant * (1 + A.energy s)) := by
  let F : ℝ := (DFT.search A d).toReal
  have hF : DFT.search A d = (F : EReal) :=
    (EReal.coe_toReal hfinite.ne (DFT.search_ne_bot A 0 hpositive d)).symm
  have herr : Tendsto (fun κ => I.C * (κ ^ 2 + CutoffProfile.bsq μ ω w κ))
      (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun κ : ℝ => κ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id'.mpr nhdsWithin_le_nhds
    simpa using ((hid.pow 2).add
      (CutoffProfile.tendsto_bsq I.dispersion_measurable I.dispersion_positive
        I.cutoff_finite)).const_mul I.C
  have hrepair (s : State) (hs : A.density s = d) (κ : ℝ) (hκ : 0 < κ)
      (hκ₀ : κ < I.κ₀) : ∃ r, A.density r = d ∧
        A.energy r ≤ A.energy s + I.C * (κ ^ 2 + CutoffProfile.bsq μ ω w κ) ∧
        number r ≤ ENNReal.ofReal (A.energy s / I.κ₀ +
          2 * ((A.energy s - F) / κ) +
          (2 * I.C) * (I.κ₀ + CutoffProfile.asq μ ω w I.κ₀)) := by
    obtain ⟨r, hr, he, hn⟩ := I.repair s κ hκ hκ₀.le
    have hsoft0 : 0 ≤ I.softEnergy s κ := by
      rw [(I.moments s).Esoft_eq]
      exact ENNReal.toReal_nonneg
    refine ⟨r, hr.trans hs, by linarith, hn.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    convert I.hard_number_bound hF hs hκ hκ₀ using 1
    ring
  obtain ⟨s, hs, he, _⟩ := attainment_of_cutoff_repair A number d hF I.κ₀_pos
    herr hrepair (hloss d)
  have he' : (A.energy s : EReal) = DFT.search A d := by rw [he, hF]
  refine ⟨s, hs, he', I.optimizer_number_bound hpositive ?_⟩
  simpa only [hs] using he'

end InfraredRepairData

end GptLean.AttainmentConstruction
