import GptLean.PhotonLocalization

/-!
Connect the derived photon localization estimates to the closure theorem.
The witnesses below contain Fock form identities, annihilation bounds,
CCR, and positive second quantization. They do not contain the sharp
combined energy inequality or the current localization estimate.
The compactness and rough bound remain separate from these two estimates.
-/

namespace GptLean.PhotonLocalization
open Filter Topology Finset
open scoped InnerProductSpace ENNReal

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type*} [Fintype ι]

/-- Concrete covariant-derivative and field vectors of a localized state.
They may be vectors in the Hilbert–Schmidt realization of a mixed state.
The exact form identity includes the discarded vacuum fluctuation. -/
structure KineticWitness (V ι : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [Fintype ι] (charge ε B K M Eloc Eel : ℝ) where
  d : ι → V
  ann : ι → V
  cre : ι → V
  q : ι → ℝ
  g : ι → ℝ
  fluct : ι → ℝ
  r : ℝ
  s : ℝ
  coulomb : ℝ
  q_nonneg : ∀ i, 0 ≤ q i
  g_nonneg : ∀ i, 0 ≤ g i
  r_nonneg : 0 ≤ r
  s_nonneg : 0 ≤ s
  q_le : ∀ i, q i ≤ ε
  g_le : ∀ i, g i ≤ ε
  fluct_le : ∀ i, |fluct i| ≤ ε
  annihilation : ∀ i, ‖ann i‖ ≤ q i * r
  ccr : ∀ i, ‖cre i‖ ^ 2 = ‖ann i‖ ^ 2 + g i ^ 2 * s ^ 2
  scale_le : 2 * r + s ≤ B
  derivative_le : ∑ i, ‖d i‖ ≤ K
  mass_le : s ^ 2 ≤ M
  localized_form : Eloc = (1 / 2 : ℝ) * ∑ i,
    (‖d i + (charge : ℂ) • (ann i + cre i)‖ ^ 2 +
      charge ^ 2 * fluct i ^ 2 * s ^ 2) + coulomb
  original_form : Eel = (1 / 2 : ℝ) * ∑ i, ‖d i‖ ^ 2 + coulomb

/-- The kinetic witness proves its local error. The coefficients are
uniform whenever `B`, `K`, and `M` are uniform on the energy sublevel. -/
theorem KineticWitness.bound {charge ε B K M Eloc Eel : ℝ}
    (W : KineticWitness V ι charge ε B K M Eloc Eel)
    (hε : 0 ≤ ε) (hB : 0 ≤ B) :
    Eloc ≤ Eel + (|charge| * B * K) * ε +
      ((Fintype.card ι : ℝ) / 2 * (charge ^ 2 * B ^ 2 + charge ^ 2 * M)) * ε ^ 2 := by
  have hf : ∀ i, ‖W.ann i + W.cre i‖ ≤ ε * B := by
    intro i
    exact (field_norm_le_cutoff _ _ (W.q_nonneg i) (W.g_nonneg i)
      W.r_nonneg W.s_nonneg (W.q_le i) (W.g_le i) (W.annihilation i) (W.ccr i)).trans
      (mul_le_mul_of_nonneg_left W.scale_le hε)
  have hkin := kinetic_localization_bound W.d (fun i => W.ann i + W.cre i)
    W.fluct (e := charge) hε hB (sq_nonneg W.s) hf W.fluct_le
  have hlin := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left W.derivative_le (mul_nonneg (abs_nonneg charge) hB)) hε
  have hquad := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (add_le_add_left (mul_le_mul_of_nonneg_left W.mass_le (sq_nonneg charge))
        (charge ^ 2 * B ^ 2)) (by positivity : 0 ≤ (Fintype.card ι : ℝ) / 2))
    (sq_nonneg ε)
  nlinarith only [hkin, hlin, hquad, W.localized_form, W.original_form]

/-- Finite-rank radiation data are shared by all states. The convergence
is needed only for each fixed truncation `k`. -/
structure RadiationFamily (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  basis : (k : ℕ) → Fin k → H
  localized : (k : ℕ) → ℕ → Fin k → H
  bessel : ∀ k z, ∑ i, ‖⟪basis k i, z⟫_ℂ‖ ^ 2 ≤ ‖z‖ ^ 2
  converges : ∀ k i, Tendsto (fun m => localized k m i) atTop (𝓝 (basis k i))

noncomputable def RadiationFamily.error (R : RadiationFamily H) (k m : ℕ) : ℝ :=
  ∑ i, (‖R.localized k m i‖ + ‖R.basis k i‖) * ‖R.localized k m i - R.basis k i‖

theorem RadiationFamily.error_nonneg (R : RadiationFamily H) (k m : ℕ) :
    0 ≤ R.error k m := by
  exact sum_nonneg fun i _ => mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (norm_nonneg _)

theorem RadiationFamily.error_zero (R : RadiationFamily H) (k : ℕ) :
    Tendsto (R.error k) atTop (𝓝 0) :=
  finite_rank_error_tendsto (R.localized k) (R.basis k) (R.converges k)

/-- A Bessel family suffices for the sharp finite-rank estimate. The
cutoff error converges strongly in the same energy representation. -/
noncomputable def RadiationFamily.ofStrongBesselError
    (basis : (k : ℕ) → Fin k → H)
    (hbessel : ∀ k z, ∑ i, ‖⟪basis k i, z⟫_ℂ‖ ^ 2 ≤ ‖z‖ ^ 2)
    (error : ℕ → H → H)
    (herror : ∀ z, Tendsto (fun m => error m z) atTop (𝓝 0)) : RadiationFamily H where
  basis := basis
  localized k m i := basis k i - error m (basis k i)
  bessel := hbessel
  converges k i := by
    simpa using tendsto_const_nhds.sub (herror (basis k i))

/-- The original orthonormal-family constructor is retained. Its Bessel
bound follows from Mathlib's finite orthonormal Bessel inequality. -/
noncomputable def RadiationFamily.ofStrongError
    (basis : (k : ℕ) → Fin k → H) (horth : ∀ k, Orthonormal ℂ (basis k))
    (error : ℕ → H → H)
    (herror : ∀ z, Tendsto (fun m => error m z) atTop (𝓝 0)) : RadiationFamily H :=
  RadiationFamily.ofStrongBesselError basis (fun k z => by
    simpa using (horth k).sum_inner_products_le (s := (univ : Finset (Fin k))) z) error herror

/-- Positivity of second quantization and of the trace is used only in
this form. The pullback identifies localized `T_k` with the finite-rank
one-photon form built from `localized`. -/
structure RadiationWitness (R : RadiationFamily H) (k m : ℕ)
    (Rloc Rrad : ℝ) : Prop where
  positive_lift : ∀ c : ℝ,
    (∀ z : H, ∑ i, ‖⟪R.localized k m i, z⟫_ℂ‖ ^ 2 ≤ c * ‖z‖ ^ 2) →
    Rloc ≤ c * Rrad

theorem RadiationWitness.bound {R : RadiationFamily H} {k m : ℕ} {Rloc Rrad : ℝ}
    (W : RadiationWitness R k m Rloc Rrad) :
    Rloc ≤ (1 + R.error k m) * Rrad := by
  apply W.positive_lift
  intro z
  exact finite_rank_radiation_bound _ _ z (R.bessel k z)

/-- A current form identity and relative field data for a mixed-state
square root. The tested-current bound is a consequence, not a field. -/
structure CurrentWitness (V ι : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [Fintype ι] (charge ε B C Jloc J : ℝ) where
  root : V
  ann : ι → V
  cre : ι → V
  test : ι → V →L[ℂ] V
  q : ι → ℝ
  g : ι → ℝ
  Z : ι → ℝ
  r : ℝ
  s : ℝ
  normalized : ‖root‖ = 1
  q_nonneg : ∀ i, 0 ≤ q i
  g_nonneg : ∀ i, 0 ≤ g i
  Z_nonneg : ∀ i, 0 ≤ Z i
  r_nonneg : 0 ≤ r
  s_nonneg : 0 ≤ s
  q_le : ∀ i, q i ≤ ε
  g_le : ∀ i, g i ≤ ε
  test_le : ∀ i, ‖test i‖ ≤ Z i
  test_sum_le : |charge| * ∑ i, Z i ≤ C
  annihilation : ∀ i, ‖ann i‖ ≤ q i * r
  ccr : ∀ i, ‖cre i‖ ^ 2 = ‖ann i‖ ^ 2 + g i ^ 2 * s ^ 2
  scale_le : 2 * r + s ≤ B
  current_identity : Jloc - J =
    (⟪root, (charge : ℂ) • ∑ i, test i (ann i + cre i)⟫_ℂ).re

theorem CurrentWitness.bound {charge ε B C Jloc J : ℝ}
    (W : CurrentWitness V ι charge ε B C Jloc J)
    (hε : 0 ≤ ε) (hC : 0 ≤ C) : |Jloc - J| ≤ C * ε * B := by
  have h := tested_current_of_fields W.root W.ann W.cre W.test W.q W.g W.Z hε
    W.r_nonneg W.s_nonneg W.q_nonneg W.g_nonneg W.Z_nonneg W.q_le W.g_le
    W.test_le W.annihilation W.ccr W.current_identity
  rw [W.normalized, one_mul] at h
  apply h.trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right W.test_sum_le hε) W.scale_le
    (by linarith [W.r_nonneg, W.s_nonneg]) (mul_nonneg hC hε)

variable {X Test : Type*} [NormedAddCommGroup X]
  {D : PhotonLoss.LocalizationData X} {T : PhotonLoss.TraceData D Test}

/-- The compactness and coarse estimate are kept separate from the sharp
energy and tested-current estimates proved from the witnesses. -/
structure CoarseData (D : PhotonLoss.LocalizationData X) (T : PhotonLoss.TraceData D Test) where
  electronicTight : (ℕ → X) → Prop
  precompact : ∀ (u : ℕ → X) (E : ℝ),
    (∀ n, u n ∈ D.states) → (∀ n, T.energy (u n) ≤ ENNReal.ofReal E) →
    electronicTight u → ∀ m, TotallyBounded (Set.range fun n => D.localize m (u n))
  rough : ℝ → ℝ
  rough_bound : ∀ E m, ∀ x ∈ D.states,
    T.energy x ≤ ENNReal.ofReal E → T.energy (D.localize m x) ≤ ENNReal.ofReal (rough E)

/-- The remaining form identifications, covariant IMS, and uniform energy
sublevel bounds needed to connect the local proofs to the closure API.
All small-field estimates are derived through the preceding witnesses. -/
structure FormData (D : PhotonLoss.LocalizationData X) (T : PhotonLoss.TraceData D Test)
    (V H ι : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]
    (epsilon : ℕ → ℕ → ℝ) where
  charge : ℝ
  radiation : RadiationFamily H
  B : ℝ → ℕ → ℝ
  K : ℝ → ℕ → ℝ
  M : ℝ → ℕ → ℝ
  cap : ℝ → ℕ → ℝ
  B_nonneg : ∀ E l, 0 ≤ B E l
  ims : ℕ → ℝ
  ims_zero : Tendsto ims atTop (𝓝 0)
  energy_forms : ∀ E e l k m, ∀ x ∈ D.states, 0 ≤ e →
    T.energy x ≤ ENNReal.ofReal E → T.energy x ≤ ENNReal.ofReal e →
    ∃ Eloc Eel Rloc Rrad : ℝ,
      T.truncatedEnergy k (T.cutoff l (D.localize m x)) = ENNReal.ofReal (Eloc + Rloc) ∧
      Nonempty (KineticWitness V ι charge (epsilon l m) (B E l) (K E l) (M E l) Eloc Eel) ∧
      RadiationWitness radiation k m Rloc Rrad ∧
      Rrad ≤ cap E l ∧ Eel + Rrad ≤ e + ims l
  testRadius : Test → ℕ
  testB : ℝ → Test → ℝ
  testC : Test → ℝ
  testC_nonneg : ∀ t, 0 ≤ testC t
  current_forms : ∀ E t m, ∀ x ∈ D.states, T.energy x ≤ ENNReal.ofReal E →
    Nonempty (CurrentWitness V ι charge (epsilon (testRadius t) m)
      (testB E t) (testC t) (T.test t (D.localize m x)) (T.test t x))

/-- This constructor supplies the actual `combined_bound` and `test_bound`
fields from the local operator identities. Neither is an input. -/
noncomputable def FormData.localizationEstimates
    {epsilon : ℕ → ℕ → ℝ} (F : FormData D T V H ι epsilon) (C : CoarseData D T)
    (hepsilon : ∀ l m, 0 ≤ epsilon l m)
    (hepsilon_zero : ∀ l, Tendsto (epsilon l) atTop (𝓝 0)) :
    PhotonLoss.LocalizationEstimates D T where
  electronicTight := C.electronicTight
  precompact := C.precompact
  rough := C.rough
  rough_bound := C.rough_bound
  imsError := F.ims
  imsError_zero := F.ims_zero
  localError E l k m := (|F.charge| * F.B E l * F.K E l) * epsilon l m +
    ((Fintype.card ι : ℝ) / 2 * (F.charge ^ 2 * F.B E l ^ 2 + F.charge ^ 2 * F.M E l)) *
      epsilon l m ^ 2 + F.radiation.error k m * F.cap E l
  localError_zero E l k := combined_error_tendsto _ _ _ _ _
    (hepsilon_zero l) (F.radiation.error_zero k)
  combined_bound E e l k m x hx he0 hE he := by
    obtain ⟨Eloc, Eel, Rloc, Rrad, hform, ⟨W⟩, hrad, hcap, hims⟩ :=
      F.energy_forms E e l k m x hx he0 hE he
    rw [hform]
    apply ENNReal.ofReal_le_ofReal
    exact combined_energy_bound (F.radiation.error_nonneg k m) hcap
      (W.bound (hepsilon l m) (F.B_nonneg E l)) hrad.bound hims
  testError E t m := F.testC t * epsilon (F.testRadius t) m * F.testB E t
  testError_zero E t := current_error_tendsto _ _ _ (hepsilon_zero (F.testRadius t))
  test_bound E t m x hx hE := by
    obtain ⟨W⟩ := F.current_forms E t m x hx hE
    exact W.bound (hepsilon _ _) (F.testC_nonneg t)

end GptLean.PhotonLocalization
