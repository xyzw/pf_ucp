import GptLean.PhysicalWeylReference
import GptLean.PhysicalPFSpectral
import GptLean.PhysicalPairTests
import GptLean.PhysicalPFVacuumInsertion

/-!
Displaced density matrices and the vanishing mean transverse electric field
(`cor-weyl-PF-shifts`, `prop-optimizer-mean-fields` (ii)).

For a finite-energy fermionic density matrix `Γ = ∑ₙ |uₙ⟩⟨uₙ|` the displaced
state `Γ_f = W(f) Γ W(f)†` is the push of `Γ` by the spatial lift of `W(f)`. Its
spectral source is `W(f) uₙ`, so it is positive, has trace one, is fermionic,
and has finite energy `∑ₙ E(W(f) uₙ)`.

A direction is real when its classical field vanishes, `2 Re ⟨κ_b(x), f⟩ = 0` for
every coordinate. Then the displacement leaves every density and current
unchanged, and `E(Γ_{tf}) = E(Γ) + 2t Re Tr(a(ω f) Γ) + t² ‖√ω f‖²`. If `Γ`
minimizes the energy at its pair, the linear coefficient vanishes:
`Re Tr(a(ω f) Γ) = 0`. Here `Tr(a(h) Γ) = ∑ₙ ⟨uₙ, a(h) uₙ⟩` for any spectral
source of `Γ`. For the smeared transverse electric field
`E_⊥(g) = -i (a†(ω g) - a(ω g))` with `g` real, the direction `f = i g` is real
and gives `Tr(E_⊥(g) Γ) = -2 Im Tr(a(ω g) Γ) = 0`.
-/

noncomputable section

namespace GptLean.PhysicalWeyl

open MeasureTheory Filter PhysicalFock PhysicalPFReference PhysicalPFSoftTag
  PhysicalNormalTrace Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000

theorem inner_shift_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (L : E ≃ₗᵢ[ℂ] E) (a c u : E) {r : ℝ} (hr : r = 0) :
    (⟪L a, L (c - (r : ℂ) • u)⟫_ℂ).re = (⟪a, c⟫_ℂ).re := by
  rw [LinearIsometryEquiv.inner_map_map, hr, Complex.ofReal_zero, zero_smul, sub_zero]

theorem linear_coefficient_zero {a b : ℝ} (hb : 0 ≤ b) (h : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b) :
    a = 0 := by
  have hb1 : 0 < b + 1 := by linarith
  have h1 := h (-a / (b + 1))
  have key : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b =
      -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
    field_simp
    ring
  rw [key] at h1
  have h2 : a ^ 2 * (b + 2) ≤ 0 := by
    have hpos : 0 < (b + 1) ^ 2 := by positivity
    have := (div_nonneg_iff.mp h1)
    rcases this with ⟨hn, _⟩ | ⟨_, hd⟩
    · linarith
    · linarith
  have h3 : a ^ 2 ≤ 0 := by nlinarith
  exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h3 (sq_nonneg a))


section States

variable {N : ℕ} (i : Fin N) (V : Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ b, AEStronglyMeasurable (κ b) volume)
  (M : ℝ) (hbound : ∀ b, ∀ᵐ x ∂volume, ‖κ b x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (e : ℝ) (W : ConcreteWeylLaw photonMeasure) {f : Lp ℂ 2 photonMeasure}
  (K : WeightedPhotonKernel)
  (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)

/-- `W(f)` on the wave functions. -/
def weylWave (W : ConcreteWeylLaw photonMeasure) (f : Lp ℂ 2 photonMeasure) :
    WaveSpace (Fin N × Fin 3) →ₗᵢ[ℂ] WaveSpace (Fin N × Fin 3) :=
  PhysicalPFVacuumInsertion.spatialLift volume (W.weyl f).toLinearIsometry

theorem weylWave_inclusion (u : Reference (Fin N × Fin 3) V) :
    weylWave W f (inclusion (Fin N × Fin 3) V u) =
      inclusion (Fin N × Fin 3) V (weylRef V W K hK u) := by
  apply Lp.ext
  filter_upwards [PhysicalPFVacuumInsertion.spatialLift_ae volume (W.weyl f).toLinearIsometry
    (inclusion (Fin N × Fin 3) V u), inclusion_weylRef_ae V W K hK u] with x h₁ h₂
  exact h₁.trans h₂.symm

/-- The displaced trace `W(f) Γ W(f)†`. -/
def weylTrace (W : ConcreteWeylLaw photonMeasure) (f : Lp ℂ 2 photonMeasure)
    (x : B.Trace (WaveSpace (Fin N × Fin 3))) : B.Trace (WaveSpace (Fin N × Fin 3)) :=
  B.push (weylWave W f).toContinuousLinearMap x

/-- The displaced spectral source. -/
def weylSource {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B x) :
    PhysicalPFSource.Source (Fin N × Fin 3) V B (weylTrace B W f x) where
  vector n := weylRef V W K hK (s.vector n)
  hasSum := by
    have h := (B.push (weylWave W f).toContinuousLinearMap).hasSum s.hasSum
    simp only [B.push_rankOne, LinearIsometry.coe_toContinuousLinearMap,
      weylWave_inclusion V W K hK] at h
    exact h

theorem weylTrace_expectation {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B x) :
    (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation (weylTrace B W f x) =
      ∑' n, ENNReal.ofReal (energy (Fin N × Fin 3) V C κ hκ M hbound e
        (weylRef V W K hK (s.vector n))) := by
  refine (congrArg (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation
    (weylSource V B W K hK s).hasSum.tsum_eq.symm).trans ?_
  refine ((normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation_tsum
      (weylSource V B W K hK s).hasSum.summable
      (fun n => (B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne_positive _)).trans ?_
  exact tsum_congr fun n => normalEnergy_rankOne (Fin N × Fin 3) V C κ hκ M hbound B S e _

include K hK in
theorem weylTrace_finite {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B x)
    (he : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation x < ⊤) :
    (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation (weylTrace B W f x) < ⊤ := by
  have hsum : Summable (fun n => 2 * energy (Fin N × Fin 3) V C κ hκ M hbound e (s.vector n) +
      ((Fintype.card (Fin N × Fin 3) * (2 * (|e| * (2 * M * ‖f‖)) ^ 2 *
        ‖inclusion (Fin N × Fin 3) V (s.vector n)‖ ^ 2)) / 2 +
          2 * ‖K.val.2‖ ^ 2 * ‖inclusion (Fin N × Fin 3) V (s.vector n)‖ ^ 2)) :=
    ((s.energy_hasSum C κ hκ M hbound S e he).summable.mul_left 2).add
      ((((s.mass_hasSum.summable.mul_left (2 * (|e| * (2 * M * ‖f‖)) ^ 2)).mul_left
        (Fintype.card (Fin N × Fin 3) : ℝ)).div_const 2).add
          (s.mass_hasSum.summable.mul_left (2 * ‖K.val.2‖ ^ 2)))
  have hle : Summable (fun n => energy (Fin N × Fin 3) V C κ hκ M hbound e
      (weylRef V W K hK (s.vector n))) :=
    Summable.of_nonneg_of_le (fun n => energy_nonneg _ _ _ _ _ _ _ e _)
      (fun n => energy_weylRef_le V W K hK C κ hκ M hbound e _) hsum
  exact (weylTrace_expectation V C κ hκ M hbound B S e W K hK s).trans_lt
    ((ENNReal.ofReal_tsum_of_nonneg (fun n => energy_nonneg _ _ _ _ _ _ _ e _) hle).symm.trans_lt
      ENNReal.ofReal_lt_top)

include K hK in
theorem weylTrace_fermionic {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : PhysicalPFSource.SupportedSource N V B x) :
    B.push (PhysicalElectronicFermions.projection N PhotonFock) (weylTrace B W f x) =
      weylTrace B W f x := by
  have h1 := (B.push (PhysicalElectronicFermions.projection N PhotonFock)).hasSum
    (weylSource V B W K hK s.toSource).hasSum
  have hP : ∀ n, PhysicalElectronicFermions.projection N PhotonFock
      (inclusion (Fin N × Fin 3) V ((weylSource V B W K hK s.toSource).vector n)) =
        inclusion (Fin N × Fin 3) V ((weylSource V B W K hK s.toSource).vector n) := fun n =>
    (PhysicalElectronicFermions.projection_eq_self_iff N PhotonFock _).mpr
      ((PhysicalElectronicFermions.mem_fermionicSubspace_iff N PhotonFock _).mp
        (inclusion_weylRef_fermionic W K hK _ (s.fermionic n)))
  simp only [B.push_rankOne, hP] at h1
  have h2 : HasSum (fun n => (B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne
      (inclusion (Fin N × Fin 3) V ((weylSource V B W K hK s.toSource).vector n)))
      (B.push (PhysicalElectronicFermions.projection N PhotonFock) (weylTrace B W f x)) := h1
  exact h2.unique (weylSource V B W K hK s.toSource).hasSum

include K hK in
/-- **The displaced density matrix** `W(f) Γ W(f)†`. -/
def weylState (m : PhysicalPFStates.MixedState V C κ hκ M hbound B S e) :
    PhysicalPFStates.MixedState V C κ hκ M hbound B S e :=
  ⟨⟨weylTrace B W f m.val.val,
    B.push_positive _ m.val.property.1,
    (B.push_trace_isometry (weylWave W f) m.val.property.1).trans m.val.property.2.1,
    weylTrace_finite V C κ hκ M hbound B S e W K hK
      (PhysicalPFStates.source V C κ hκ M hbound B S e m.val.val m.val.property.1
        m.val.property.2.2) m.val.property.2.2⟩,
    weylTrace_fermionic V B W K hK (Classical.choice (PhysicalPFSource.supported_source_exists
      N V B C κ hκ M hbound S e m.val.property.1 m.val.property.2.2 m.property))⟩

theorem weylState_energy_hasSum (m : PhysicalPFStates.MixedState V C κ hκ M hbound B S e)
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B m.val.val) :
    HasSum (fun n => energy (Fin N × Fin 3) V C κ hκ M hbound e (weylRef V W K hK (s.vector n)))
      ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).energy
        (weylState V C κ hκ M hbound B S e W K hK m)) :=
  (weylSource V B W K hK s).energy_hasSum C κ hκ M hbound S e
    (weylState V C κ hκ M hbound B S e W K hK m).val.property.2.2

theorem weylState_pair_hasSum (m : PhysicalPFStates.MixedState V C κ hκ M hbound B S e)
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B m.val.val) :
    HasSum (fun n => PhysicalPFPairSeries.vectorPair i V C κ hκ M hbound e
        (weylRef V W K hK (s.vector n)))
      ((PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density
        (weylState V C κ hκ M hbound B S e W K hK m)) :=
  PhysicalPFSpectral.mixed_pair_hasSum i V C κ hκ M hbound B S e
    (weylState V C κ hκ M hbound B S e W K hK m) (weylSource V B W K hK s)

/-- A real displacement keeps the pair of every reference vector. -/
theorem vectorPair_weylRef_of_real
    (hreal : ∀ b, ∀ᵐ x ∂volume, classicalField κ f b x = 0) (u : Reference (Fin N × Fin 3) V) :
    PhysicalPFPairSeries.vectorPair i V C κ hκ M hbound e (weylRef V W K hK u) =
      PhysicalPFPairSeries.vectorPair i V C κ hκ M hbound e u := by
  apply PhysicalPairSpace.pair_eq_of_bounded_spatial_tests
  · intro t
    refine (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V (weylRef V W K hK u)))
      (fun a => covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, a) (weylRef V W K hK u))
      t.weight t.measurable (ae_of_all _ t.bounded)).trans (Eq.trans ?_
        (PhysicalSourcePair.tested_density_ofWaveFunction i
          (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
          (fun a => covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, a) u)
          t.weight t.measurable (ae_of_all _ t.bounded)).symm)
    refine congrArg (fun r : ℝ => (N : ℝ) * r) (integral_congr_ae ?_)
    filter_upwards [inclusion_weylRef_ae V W K hK u] with z hz
    exact congrArg (fun r : ℝ => t.weight ((PhysicalSourceCoordinates.split i) z).1 * r ^ 2)
      ((congrArg norm hz).trans (LinearIsometryEquiv.norm_map _ _))
  · intro b t
    refine (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V (weylRef V W K hK u)))
      (fun a => covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, a) (weylRef V W K hK u)) b
      t.weight t.measurable (ae_of_all _ t.bounded)).trans (Eq.trans ?_
        (PhysicalSourcePair.tested_current_ofWaveFunction i
          (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
          (fun a => covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, a) u) b
          t.weight t.measurable (ae_of_all _ t.bounded)).symm)
    refine congrArg (fun r : ℝ => (N : ℝ) * r) (integral_congr_ae ?_)
    filter_upwards [inclusion_weylRef_ae V W K hK u,
      covariant_weylRef_ae V W K hK C κ hκ M hbound e (i, b) u, hreal (i, b)] with z h₁ h₂ h₃
    change t.weight _ * (⟪inclusion (Fin N × Fin 3) V (weylRef V W K hK u) z,
      covariant (Fin N × Fin 3) V C κ hκ M hbound e (i, b) (weylRef V W K hK u) z⟫_ℂ).re = _
    refine (congrArg₂ (fun a c => t.weight ((PhysicalSourceCoordinates.split i) z).1 *
      (⟪a, c⟫_ℂ).re) h₁ h₂).trans ?_
    exact congrArg (fun r : ℝ => t.weight ((PhysicalSourceCoordinates.split i) z).1 * r)
      (inner_shift_zero (W.weyl f) _ _ _ (by rw [h₃, mul_zero]))

theorem weylState_density_of_real (hreal : ∀ b, ∀ᵐ x ∂volume, classicalField κ f b x = 0)
    (m : PhysicalPFStates.MixedState V C κ hκ M hbound B S e) :
    (PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density
        (weylState V C κ hκ M hbound B S e W K hK m) =
      (PhysicalPFStates.mixedModel i V C κ hκ M hbound B S e).density m := by
  let s := PhysicalPFStates.source V C κ hκ M hbound B S e m.val.val m.val.property.1
    m.val.property.2.2
  have h1 := weylState_pair_hasSum i V C κ hκ M hbound B S e W K hK m s
  simp only [vectorPair_weylRef_of_real i V C κ hκ M hbound e W K hK hreal] at h1
  exact h1.unique (PhysicalPFSpectral.mixed_pair_hasSum i V C κ hκ M hbound B S e m s)

/-- The coherent amplitude `Tr(a(k₁) Γ) = ∑ₙ ⟨uₙ, a(k₁) uₙ⟩` of a spectral source. -/
def sourceAmplitude {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B x) (k : WeightedPhotonKernel) : ℂ :=
  ∑' n, ⟪inclusion (Fin N × Fin 3) V (s.vector n), annihilationRef V k (s.vector n)⟫_ℂ

end States

end GptLean.PhysicalWeyl
