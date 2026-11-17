import GptLean.PhotonLocalizationKineticChannel
import GptLean.PhotonLocalizationSharpRadiation
import GptLean.PhotonLocalizationFreeEnergy

/-!
The combined sharp energy estimate on one normal channel.

Kinetic graph vectors, the electronic potential and the finite-rank
radiation form are evaluated on the same Kraus output. All estimates
remain in nonnegative extended reals until the final finite bound. The
coefficient on the original energy is one before taking any limit.
-/

namespace GptLean.PhotonLocalization

open Filter Topology
open PhotonLocalizationChannel PhotonLocalizationFockChannel
open PhotonLocalizationFormBounds PhotonLocalizationFreeEnergy
open scoped InnerProductSpace ENNReal

variable {h H V X Q ι : Type*}
  [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Fintype ι]
  {A : Gaussian.RankOneData H X} {Tr : RemovalState.PositiveTraceData X}
  {F : FockFactorization h H}

/-- Source-sensitive lifting is needed after an electronic cutoff. The
small kernel estimate is required only on its actual supported spectral
vectors, rather than on arbitrary vectors throughout configuration space. -/
theorem channel_kinetic_of_spectral_dilations
    (N : NormalTraceData A) (kinetic control : RemovalState.PositiveForm Tr)
    (hpositive : A.positive ⊆ Tr.positive) (U : KrausIsometry H)
    {charge ε B K : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B) (hK : 0 ≤ K)
    {x : X} (v : ℕ → H) (hv : HasSum (fun n => A.rankOne (v n)) x)
    (sources : ∀ n, control.expectation (A.rankOne (v n)) < ⊤ →
      Nonempty (KineticDilationSource (A := A) (ι := ι) kinetic control U
        (v n) charge ε B K))
    (hfinite : control.expectation x < ⊤) :
    kinetic.expectation (N.extend U x) ≤ kinetic.expectation x +
      ENNReal.ofReal (kineticError ι charge B K ε) * control.expectation x := by
  have hexp (E : RemovalState.PositiveForm Tr) :
      E.expectation x = ∑' n, E.expectation (A.rankOne (v n)) := by
    rw [← hv.tsum_eq, E.expectation_tsum hv.summable
      (fun n => hpositive (A.rankOne_positive (v n)))]
  have hfiniteVector (n : ℕ) : control.expectation (A.rankOne (v n)) < ⊤ := by
    apply lt_of_le_of_lt (ENNReal.le_tsum n) _
    rwa [← hexp control]
  have hout := N.extend_hasSum U hv
  rw [← hout.tsum_eq, kinetic.expectation_tsum hout.summable
    (fun n => hpositive (pure_positive A U (v n))),
    hexp kinetic, hexp control, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro n
  obtain ⟨S⟩ := sources n (hfiniteVector n)
  exact S.bound hpositive hε hB hK

/-- The positive-form version of the combined estimate, derived from
the same-channel kinetic and radiation constructions. The source can
already be electronically cut and need not have trace one. -/
theorem sharp_channel_energy_bound
    (D : FockFormCalculus A Tr F Q) (N : NormalTraceData A)
    (hpositive : A.positive ⊆ Tr.positive)
    (kinetic potential control : RemovalState.PositiveForm Tr)
    (R : RadiationFamily V) (radiation : Q) (truncation : ℕ → Q)
    (m k : ℕ) (j : h →ₗᵢ[ℂ] WithLp 2 (h × h))
    (modes : Fin k → h)
    (htruncation : ∀ u, D.value (truncation k) u =
      ENNReal.ofReal (∑ i, ‖⟪modes i, u⟫_ℂ‖ ^ 2))
    (hduality : ∀ u, D.value radiation u < ⊤ → ∃ z : V,
      D.value radiation u = ENNReal.ofReal (‖z‖ ^ 2) ∧
      ∀ i, ⟪modes i, retainedMap j u⟫_ℂ = ⟪R.localized k m i, z⟫_ℂ)
    (W : ℕ → H →L[ℂ] H)
    (hWtrace : ∀ n v, (potential.truncation n (A.rankOne v) : ℂ) = inner ℂ v (W n v))
    (hW : ∀ n v a, F.factor j (W n v) a = W n (F.factor j v a))
    {charge ε B K e cap radCap : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (he : 0 ≤ e) (hcap : 0 ≤ cap) (hradCap : 0 ≤ radCap)
    (sources : ∀ v, control.expectation (A.rankOne v) < ⊤ →
      Nonempty (KineticDilationSource (A := A) (ι := ι) kinetic control (F.factor j)
        v charge ε B K))
    {x : X} (hx : x ∈ A.positive)
    (hcontrol : control.expectation x ≤ ENNReal.ofReal cap)
    (hradiation : (D.observable radiation).expectation x ≤ ENNReal.ofReal radCap)
    (hsource : kinetic.expectation x + potential.expectation x +
      (D.observable radiation).expectation x ≤ ENNReal.ofReal e) :
    kinetic.expectation (N.extend (F.factor j) x) +
      potential.expectation (N.extend (F.factor j) x) +
      (D.observable (truncation k)).expectation (N.extend (F.factor j) x) ≤
        ENNReal.ofReal (e + kineticError ι charge B K ε * cap + R.error k m * radCap) := by
  have hkin := channel_kinetic_of_dilations N kinetic control hpositive (F.factor j)
    hε hB hK sources hx (hcontrol.trans_lt ENNReal.ofReal_lt_top)
  have hpot := electronic_form_preserved N potential (F.factor j) W hWtrace hW hx
  have hrad := sharp_channel_radiation_bound D N hpositive R radiation truncation
    m k j modes htruncation hduality hx
  have herror := kineticError_nonneg (ι := ι) (charge := charge) hB hK hε
  have hδ := R.error_nonneg k m
  rw [hpot]
  calc
    _ ≤ (kinetic.expectation x + ENNReal.ofReal (kineticError ι charge B K ε) *
        control.expectation x) + potential.expectation x +
        ENNReal.ofReal (1 + R.error k m) * (D.observable radiation).expectation x :=
      add_le_add (add_le_add hkin le_rfl) hrad
    _ = (kinetic.expectation x + potential.expectation x +
        (D.observable radiation).expectation x) +
        ENNReal.ofReal (kineticError ι charge B K ε) * control.expectation x +
        ENNReal.ofReal (R.error k m) * (D.observable radiation).expectation x := by
      rw [ENNReal.ofReal_add (by norm_num) hδ, ENNReal.ofReal_one]
      ring
    _ ≤ ENNReal.ofReal e + ENNReal.ofReal (kineticError ι charge B K ε) *
        ENNReal.ofReal cap + ENNReal.ofReal (R.error k m) * ENNReal.ofReal radCap :=
      add_le_add (add_le_add hsource (mul_le_mul_right hcontrol _))
        (mul_le_mul_right hradiation _)
    _ = _ := by
      rw [← ENNReal.ofReal_mul herror, ← ENNReal.ofReal_mul hδ,
        ← ENNReal.ofReal_add he (mul_nonneg herror hcap),
        ← ENNReal.ofReal_add (add_nonneg he (mul_nonneg herror hcap))
          (mul_nonneg hδ hradCap)]

/-- The combined error vanishes with the electronic region and radiation
rank fixed. No interchange with the radiation-rank limit is asserted. -/
theorem sharp_channel_energy_error_zero
    (R : RadiationFamily V) (k : ℕ) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (charge B K cap radCap : ℝ) :
    Tendsto (fun m => kineticError ι charge B K (ε m) * cap + R.error k m * radCap)
      atTop (𝓝 0) := by
  have hkin : Tendsto (fun m => kineticError ι charge B K (ε m)) atTop (𝓝 0) := by
    simpa only [kineticError, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      (hε.const_mul (|charge| * B * K)).add
        ((hε.pow 2).const_mul ((Fintype.card ι : ℝ) / 2 * (charge ^ 2 * B ^ 2 + charge ^ 2)))
  simpa only [zero_mul, zero_add] using
    (hkin.mul_const cap).add ((R.error_zero k).mul_const radCap)

/-- The signed-potential version covers attractive electronic potentials.
Both potential parts are finite on the source and preserved by the same
channel. No lower bound for the multiplication potential is required.
Output kinetic, potential and truncated radiation finiteness are proved
before the real-valued energy estimate. -/
theorem sharp_channel_signed_energy_bound
    (D : FockFormCalculus A Tr F Q) (N : NormalTraceData A)
    (hpositive : A.positive ⊆ Tr.positive)
    (kinetic control : RemovalState.PositiveForm Tr)
    (potential : Bool → RemovalState.PositiveForm Tr)
    (R : RadiationFamily V) (radiation : Q) (truncation : ℕ → Q)
    (m k : ℕ) (j : h →ₗᵢ[ℂ] WithLp 2 (h × h))
    (modes : Fin k → h)
    (htruncation : ∀ u, D.value (truncation k) u =
      ENNReal.ofReal (∑ i, ‖⟪modes i, u⟫_ℂ‖ ^ 2))
    (hduality : ∀ u, D.value radiation u < ⊤ → ∃ z : V,
      D.value radiation u = ENNReal.ofReal (‖z‖ ^ 2) ∧
      ∀ i, ⟪modes i, retainedMap j u⟫_ℂ = ⟪R.localized k m i, z⟫_ℂ)
    (W : Bool → ℕ → H →L[ℂ] H)
    (hWtrace : ∀ b n v, ((potential b).truncation n (A.rankOne v) : ℂ) =
      inner ℂ v (W b n v))
    (hW : ∀ b n v a, F.factor j (W b n v) a = W b n (F.factor j v a))
    {charge ε B K e cap radCap : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hcap : 0 ≤ cap) (hradCap : 0 ≤ radCap)
    {x : X} (hx : x ∈ A.positive)
    (v : ℕ → H) (hv : HasSum (fun n => A.rankOne (v n)) x)
    (sources : ∀ n, control.expectation (A.rankOne (v n)) < ⊤ →
      Nonempty (KineticDilationSource (A := A) (ι := ι) kinetic control (F.factor j)
        (v n) charge ε B K))
    (hkinetic : kinetic.expectation x < ⊤)
    (hpotential : ∀ b, (potential b).expectation x < ⊤)
    (hcontrol : control.expectation x ≤ ENNReal.ofReal cap)
    (hradiation : (D.observable radiation).expectation x ≤ ENNReal.ofReal radCap)
    (hsource : (kinetic.expectation x).toReal +
      ((potential true).expectation x).toReal - ((potential false).expectation x).toReal +
      ((D.observable radiation).expectation x).toReal ≤ e) :
    let y := N.extend (F.factor j) x
    kinetic.expectation y < ⊤ ∧
      (∀ b, (potential b).expectation y < ⊤) ∧
      (D.observable (truncation k)).expectation y < ⊤ ∧
      (kinetic.expectation y).toReal + ((potential true).expectation y).toReal -
        ((potential false).expectation y).toReal +
        ((D.observable (truncation k)).expectation y).toReal ≤
          e + kineticError ι charge B K ε * cap + R.error k m * radCap := by
  dsimp only
  have herror := kineticError_nonneg (ι := ι) (charge := charge) hB hK hε
  have hcontrolFinite := hcontrol.trans_lt ENNReal.ofReal_lt_top
  have hk := channel_kinetic_of_spectral_dilations N kinetic control hpositive (F.factor j)
    hε hB hK v hv sources hcontrolFinite
  have hk' : kinetic.expectation (N.extend (F.factor j) x) ≤
      kinetic.expectation x + ENNReal.ofReal (kineticError ι charge B K ε * cap) := by
    apply hk.trans
    rw [ENNReal.ofReal_mul herror]
    exact add_le_add le_rfl (mul_le_mul_right hcontrol _)
  have hsumFinite : kinetic.expectation x +
      ENNReal.ofReal (kineticError ι charge B K ε * cap) < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨hkinetic, ENNReal.ofReal_lt_top⟩
  have hkReal := ENNReal.toReal_mono hsumFinite.ne hk'
  rw [ENNReal.toReal_add hkinetic.ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (mul_nonneg herror hcap)] at hkReal
  have hpot (b : Bool) := electronic_form_preserved N (potential b) (F.factor j)
    (W b) (hWtrace b) (hW b) hx
  obtain ⟨hrFinite, hrReal⟩ := sharp_channel_radiation_toReal D N hpositive R
    radiation truncation m k j modes htruncation hduality hx
      (hradiation.trans_lt ENNReal.ofReal_lt_top)
  have hrCap := ENNReal.toReal_mono ENNReal.ofReal_ne_top hradiation
  rw [ENNReal.toReal_ofReal hradCap] at hrCap
  refine ⟨hk'.trans_lt hsumFinite, fun b => by rw [hpot]; exact hpotential b,
    hrFinite, ?_⟩
  rw [hpot true, hpot false]
  have hradError := mul_le_mul_of_nonneg_left hrCap (R.error_nonneg k m)
  nlinarith

end GptLean.PhotonLocalization
