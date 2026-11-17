import GptLean.PhotonLocalizationFormBoundsFock

/-!
The free-form bound for the physical photon localization channel.
Electronic kinetic energy is preserved by proving equality for every
bounded spectral truncation and then taking the supremum. Trace
preservation and the radiation estimate give a uniform free-form bound
on the same positive output operator used by local compactness.
-/

namespace GptLean.PhotonLocalizationFreeEnergy

open Filter Topology MeasureTheory
open scoped ENNReal
open PhotonLocalizationChannel PhotonLocalizationFockChannel
open PhotonLocalizationKernelCutoffs PhotonLocalizationFormBounds

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T} {Tr : RemovalState.PositiveTraceData T}
  (N : NormalTraceData R)

/-- Electronic bounded spectral approximants are represented by their
actual operators on vectors. Kraus intertwining preserves each trace
pairing, and the supremum proves the full unbounded kinetic identity.
No finite kinetic-energy assumption is needed. -/
theorem electronic_form_preserved (kinetic : RemovalState.PositiveForm Tr)
    (U : KrausIsometry H) (W : ℕ → H →L[ℂ] H)
    (hWtrace : ∀ m v, (kinetic.truncation m (R.rankOne v) : ℂ) = inner ℂ v (W m v))
    (hW : ∀ m v a, U (W m v) a = W m (U v a))
    {x : T} (hx : x ∈ R.positive) :
    kinetic.expectation (N.extend U x) = kinetic.expectation x := by
  unfold RemovalState.PositiveForm.expectation
  apply iSup_congr
  intro m
  apply congrArg ENNReal.ofReal
  apply Complex.ofReal_injective
  have he := N.electronic U (W m) (Complex.ofRealCLM.comp (kinetic.truncation m))
    (by intro v; simpa using hWtrace m v) (hW m) hx
  simpa using he

/-- The universal free-form decomposition combines the independently
proved electronic and photon identities. The estimate retains infinity
and therefore proves form-domain preservation whenever the source form
is finite. -/
theorem free_form_le (free kinetic radiation : RemovalState.PositiveForm Tr)
    (hfree : ∀ y ∈ R.positive, free.expectation y =
      ENNReal.ofReal (R.trace y) + kinetic.expectation y + radiation.expectation y)
    (U : KrausIsometry H) (W : ℕ → H →L[ℂ] H)
    (hWtrace : ∀ m v, (kinetic.truncation m (R.rankOne v) : ℂ) = inner ℂ v (W m v))
    (hW : ∀ m v a, U (W m v) a = W m (U v a))
    {C : ℝ≥0∞} (hC : 1 ≤ C) {x : T} (hx : x ∈ R.positive)
    (hrad : radiation.expectation (N.extend U x) ≤ C * radiation.expectation x) :
    free.expectation (N.extend U x) ≤ C * free.expectation x := by
  rw [hfree _ (N.positive U hx), N.trace U hx,
    electronic_form_preserved N kinetic U W hWtrace hW hx, hfree _ hx]
  have hbase : ENNReal.ofReal (R.trace x) + kinetic.expectation x ≤
      C * (ENNReal.ofReal (R.trace x) + kinetic.expectation x) := by
    simpa only [one_mul] using
      mul_le_mul_left hC (ENNReal.ofReal (R.trace x) + kinetic.expectation x)
  calc
    _ ≤ C * (ENNReal.ofReal (R.trace x) + kinetic.expectation x) +
        C * radiation.expectation x := add_le_add hbase hrad
    _ = _ := (mul_add _ _ _).symm

/-- A real source bound gives exactly the numerical hypothesis used by
the physical compactness endpoint. The larger of one and the radiation
constant controls the unchanged mass and electronic kinetic terms. -/
theorem free_energy_bound (free kinetic radiation : RemovalState.PositiveForm Tr)
    (hfree : ∀ y ∈ R.positive, free.expectation y =
      ENNReal.ofReal (R.trace y) + kinetic.expectation y + radiation.expectation y)
    (U : KrausIsometry H) (W : ℕ → H →L[ℂ] H)
    (hWtrace : ∀ m v, (kinetic.truncation m (R.rankOne v) : ℂ) = inner ℂ v (W m v))
    (hW : ∀ m v a, U (W m v) a = W m (U v a))
    {C E : ℝ} {x : T} (hx : x ∈ R.positive)
    (hrad : radiation.expectation (N.extend U x) ≤ ENNReal.ofReal C * radiation.expectation x)
    (hsource : free.expectation x ≤ ENNReal.ofReal E) :
    free.expectation (N.extend U x) ≤ ENNReal.ofReal (max 1 C * E) := by
  have hC : 1 ≤ ENNReal.ofReal (max 1 C) := ENNReal.one_le_ofReal.mpr (le_max_left _ _)
  have hr : radiation.expectation (N.extend U x) ≤
      ENNReal.ofReal (max 1 C) * radiation.expectation x :=
    hrad.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right 1 C)) _)
  have hbound := free_form_le N free kinetic radiation hfree U W hWtrace hW hC hx hr
  calc
    _ ≤ ENNReal.ofReal (max 1 C) * free.expectation x := hbound
    _ ≤ ENNReal.ofReal (max 1 C) * ENNReal.ofReal E := mul_le_mul_right hsource _
    _ = ENNReal.ofReal (max 1 C * E) :=
      (ENNReal.ofReal_mul (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 C))).symm

omit [CompleteSpace T] in
/-- The ordinary PF/free form equivalence supplies the original free
bound for a normalized source. The equivalence is uniform over all
positive operators and is independent of photon localization. -/
theorem source_free_bound_of_pf (free : RemovalState.PositiveForm Tr)
    (pf : T → ℝ≥0∞) {A E : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hequivalence : ∀ y ∈ R.positive, free.expectation y ≤
      ENNReal.ofReal A * (pf y + ENNReal.ofReal (R.trace y)))
    {x : T} (hx : x ∈ N.states) (hpf : pf x ≤ ENNReal.ofReal E) :
    free.expectation x ≤ ENNReal.ofReal (A * (E + 1)) := by
  have hfree := hequivalence x hx.1
  rw [hx.2, ENNReal.ofReal_one] at hfree
  calc
    _ ≤ ENNReal.ofReal A * (pf x + 1) := hfree
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal E + 1) :=
      mul_le_mul_right (add_le_add_left hpf 1) _
    _ = ENNReal.ofReal (A * (E + 1)) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hE (by norm_num),
        ← ENNReal.ofReal_mul hA]

section Physical

variable {P E Q : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [MeasurableSpace P] [BorelSpace P] {μ : Measure P}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [SMulCommClass ℝ ℂ E]
  {F : FockFactorization (Lp E 2 μ) H}

/-- The actual smooth photon channel satisfies the required free-form
bound using the proved radiation-core lifting theorem and electronic
spectral approximants. Its output can be passed directly to
`normalSources_totallyBounded`. -/
theorem localized_free_energy_of_core (D : FockFormCalculus R Tr F Q)
    (hpositive : R.positive ⊆ Tr.positive) (radiation : Q)
    (free kinetic : RemovalState.PositiveForm Tr)
    (hfree : ∀ y ∈ R.positive, free.expectation y = ENNReal.ofReal (R.trace y) +
      kinetic.expectation y + (D.observable radiation).expectation y)
    (core : Set (Lp E 2 μ)) (hlsc : LowerSemicontinuous (D.value radiation))
    (happrox : ∀ u, D.value radiation u < ⊤ → ∃ v : ℕ → Lp E 2 μ,
      (∀ n, v n ∈ core) ∧ Tendsto v atTop (𝓝 u) ∧
        Tendsto (fun n => D.value radiation (v n)) atTop (𝓝 (D.value radiation u)))
    (r : ℝ) {C E₀ : ℝ} (hC : 0 < C)
    (hcore : ∀ u ∈ core,
      D.value radiation (retainedOperator r u) ≤ ENNReal.ofReal C * D.value radiation u)
    (W : ℕ → H →L[ℂ] H)
    (hWtrace : ∀ m v, (kinetic.truncation m (R.rankOne v) : ℂ) = inner ℂ v (W m v))
    (hW : ∀ m v a, F.factor (complexOnePhotonIsometry r) (W m v) a =
      W m (F.factor (complexOnePhotonIsometry r) v a))
    {x : T} (hx : x ∈ R.positive) (hsource : free.expectation x ≤ ENNReal.ofReal E₀) :
    free.expectation (N.extend (F.factor (complexOnePhotonIsometry r)) x) ≤
      ENNReal.ofReal (max 1 C * E₀) := by
  exact free_energy_bound N free kinetic (D.observable radiation) hfree
    (F.factor (complexOnePhotonIsometry r)) W hWtrace hW hx
    (localized_radiation_le_of_core D N hpositive radiation core hlsc happrox r hC hcore hx)
    hsource

end Physical

end GptLean.PhotonLocalizationFreeEnergy
