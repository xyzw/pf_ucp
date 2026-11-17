import GptLean.PhotonLocalizationModel
import GptLean.PhotonLocalizationFormBoundsFock

/-!
Sharp finite-rank radiation control on the constructed normal channel.

The one-photon inputs are the finite-rank quadratic form and the usual
duality between the radiation square root and its negative Sobolev
representation. Bessel's inequality supplies the order, and the existing
Fock calculus lifts it through all sectors and the original source series.
No mixed-state radiation witness or localized radiation bound is assumed.
-/

namespace GptLean.PhotonLocalization

open PhotonLocalizationChannel PhotonLocalizationFockChannel
open PhotonLocalizationFormBounds
open scoped InnerProductSpace ENNReal

variable {h H T Q V : Type*}
  [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {A : Gaussian.RankOneData H T} {Tr : RemovalState.PositiveTraceData T}
  {F : FockFactorization h H}

omit [CompleteSpace T] in
/-- The exact finite-rank form and square-root pairing give the sharp
one-photon inequality. Infinite radiation energy is allowed. -/
theorem sharp_onePhoton_bound
    (D : FockFormCalculus A Tr F Q) (R : RadiationFamily V)
    (radiation : Q) (truncation : ℕ → Q)
    (m k : ℕ) (j : h →ₗᵢ[ℂ] WithLp 2 (h × h))
    (modes : Fin k → h)
    (htruncation : ∀ u, D.value (truncation k) u =
      ENNReal.ofReal (∑ i, ‖⟪modes i, u⟫_ℂ‖ ^ 2))
    (hduality : ∀ u, D.value radiation u < ⊤ → ∃ z : V,
      D.value radiation u = ENNReal.ofReal (‖z‖ ^ 2) ∧
      ∀ i, ⟪modes i, retainedMap j u⟫_ℂ = ⟪R.localized k m i, z⟫_ℂ)
    (u : h) :
    D.value (truncation k) (retainedMap j u) ≤
      ENNReal.ofReal (1 + R.error k m) * D.value radiation u := by
  by_cases hfinite : D.value radiation u < ⊤
  · obtain ⟨z, hz, hpair⟩ := hduality u hfinite
    rw [htruncation, hz, ← ENNReal.ofReal_mul (by linarith [R.error_nonneg k m])]
    apply ENNReal.ofReal_le_ofReal
    simpa only [hpair, RadiationFamily.error] using
      finite_rank_radiation_bound (R.localized k m) (R.basis k) z
        (R.bessel k z)
  · have hinfinite : D.value radiation u = ⊤ := top_unique (not_lt.mp hfinite)
    have hpositive : ENNReal.ofReal (1 + R.error k m) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by linarith [R.error_nonneg k m])).ne'
    simp [hinfinite, hpositive]

/-- Sharp radiation comparison for the same normal channel that supplies
the Kraus output and local compactness. The source may have infinite
mean number. The approximation rank remains fixed during localization. -/
theorem sharp_channel_radiation_bound
    (D : FockFormCalculus A Tr F Q) (N : NormalTraceData A)
    (hpositive : A.positive ⊆ Tr.positive)
    (R : RadiationFamily V) (radiation : Q) (truncation : ℕ → Q)
    (m k : ℕ) (j : h →ₗᵢ[ℂ] WithLp 2 (h × h))
    (modes : Fin k → h)
    (htruncation : ∀ u, D.value (truncation k) u =
      ENNReal.ofReal (∑ i, ‖⟪modes i, u⟫_ℂ‖ ^ 2))
    (hduality : ∀ u, D.value radiation u < ⊤ → ∃ z : V,
      D.value radiation u = ENNReal.ofReal (‖z‖ ^ 2) ∧
      ∀ i, ⟪modes i, retainedMap j u⟫_ℂ = ⟪R.localized k m i, z⟫_ℂ)
    {x : T} (hx : x ∈ A.positive) :
    (D.observable (truncation k)).expectation (N.extend (F.factor j) x) ≤
      ENNReal.ofReal (1 + R.error k m) * (D.observable radiation).expectation x := by
  exact D.channel_bound N hpositive j (truncation k) radiation
    (sharp_onePhoton_bound D R radiation truncation m k j modes htruncation hduality) hx

/-- Conversion to real form values is made only after proving the
localized expectation finite. This supplies the real radiation comparison
used by the combined energy estimate without assuming output finiteness. -/
theorem sharp_channel_radiation_toReal
    (D : FockFormCalculus A Tr F Q) (N : NormalTraceData A)
    (hpositive : A.positive ⊆ Tr.positive)
    (R : RadiationFamily V) (radiation : Q) (truncation : ℕ → Q)
    (m k : ℕ) (j : h →ₗᵢ[ℂ] WithLp 2 (h × h))
    (modes : Fin k → h)
    (htruncation : ∀ u, D.value (truncation k) u =
      ENNReal.ofReal (∑ i, ‖⟪modes i, u⟫_ℂ‖ ^ 2))
    (hduality : ∀ u, D.value radiation u < ⊤ → ∃ z : V,
      D.value radiation u = ENNReal.ofReal (‖z‖ ^ 2) ∧
      ∀ i, ⟪modes i, retainedMap j u⟫_ℂ = ⟪R.localized k m i, z⟫_ℂ)
    {x : T} (hx : x ∈ A.positive)
    (hfinite : (D.observable radiation).expectation x < ⊤) :
    (D.observable (truncation k)).expectation (N.extend (F.factor j) x) < ⊤ ∧
    ((D.observable (truncation k)).expectation (N.extend (F.factor j) x)).toReal ≤
      (1 + R.error k m) * ((D.observable radiation).expectation x).toReal := by
  have hbound := sharp_channel_radiation_bound D N hpositive R radiation truncation
    m k j modes htruncation hduality hx
  have hright : ENNReal.ofReal (1 + R.error k m) *
      (D.observable radiation).expectation x < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite
  refine ⟨hbound.trans_lt hright, ?_⟩
  have hreal := ENNReal.toReal_mono hright.ne hbound
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith [R.error_nonneg k m] : 0 ≤ 1 + R.error k m)]
    using hreal

end GptLean.PhotonLocalization
