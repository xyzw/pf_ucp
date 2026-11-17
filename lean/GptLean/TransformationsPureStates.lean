import GptLean.PhysicalPFStates
import GptLean.PhysicalPFParticle
import GptLean.PhysicalPFDomain
import GptLean.Transformations

/-!
Pure states of the constructed particle-kernel Pauli--Fierz model and a
generic covariance theorem for the pure Levy--Lieb functional.

The model has N electrons, the physical photon Fock space, the spatial field
with kernel `K(·, xⱼ)` at the actual particle positions, and the closed
common Pauli--Fierz graph. Pure states are normalized fermionic vectors of
finite normal energy. Every pure state is the inclusion of a reference-domain
vector, its energy is the reference energy, and its density-current pair is
the constructed wave-function pair `PhysicalPFParticle.pair`.

Consequently a bijection of wave functions that preserves norms and the
fermionic subspace, lifts to the reference domain, and transforms energy and
pair by `energy ↦ energy + ℓ(pair)` and `pair ↦ τ(pair)` gives
`F_LL(τ d) = F_LL(d) + ℓ(d)` for every pair, including empty fibres. This is
the common final step of the proofs in `app-transformation-properties`.
-/

noncomputable section

namespace GptLean.TransformationsPureStates

open MeasureTheory PhysicalFock PhysicalPFReference SymmetricLift PhysicalPairSpace
  PhysicalNormalTrace PhysicalClosedForms
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000
set_option Elab.async false

variable {N : ℕ} (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ) (i : Fin N)

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM

/-- Pure states of the constructed particle-kernel Pauli--Fierz model. -/
abbrev PureState := PhysicalPFStates.PureState V C κP hκP M hbP B S e

/-- The pure-state constrained-search model. -/
abbrev pureModel := PhysicalPFStates.pureModel i V C κP hκP M hbP B S e

theorem pure_reference (v : PureState V C K hK M hM B S e) :
    ∃ u : Reference (Fin N × Fin 3) V, inclusion (Fin N × Fin 3) V u = v.val :=
  (PhysicalPFRadiation.normalEnergy_rankOne_finite_iff (Fin N × Fin 3) V C κP hκP M hbP B S e
    v.val).mp v.property.2.2

theorem pure_fermionic (v : PureState V C K hK M hM B S e) :
    v.val ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
  (PhysicalElectronicFermions.mem_fermionicSubspace_iff N PhotonFock v.val).mpr
    ((PhysicalElectronicFermions.projection_eq_self_iff N PhotonFock v.val).mp v.property.2.1)

/-- A normalized fermionic reference vector is a pure state. -/
def ofVector (v : WaveSpace (Fin N × Fin 3)) (hv : ‖v‖ = 1)
    (hf : v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
    (hr : ∃ u : Reference (Fin N × Fin 3) V, inclusion (Fin N × Fin 3) V u = v) :
    PureState V C K hK M hM B S e :=
  ⟨v, hv, (PhysicalElectronicFermions.projection_eq_self_iff N PhotonFock v).mpr
      ((PhysicalElectronicFermions.mem_fermionicSubspace_iff N PhotonFock v).mp hf),
    (PhysicalPFRadiation.normalEnergy_rankOne_finite_iff (Fin N × Fin 3) V C κP hκP M hbP B S e
      v).mpr hr⟩

theorem pure_energy (v : PureState V C K hK M hM B S e) (u : Reference (Fin N × Fin 3) V)
    (hu : inclusion (Fin N × Fin 3) V u = v.val) :
    (pureModel V C K hK M hM B S e i).energy v =
      energy (Fin N × Fin 3) V C κP hκP M hbP e u := by
  change ((PhysicalPFStates.energy V C κP hκP M hbP B S e).expectation
    ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne v.val)).toReal = _
  rw [← hu, normalEnergy_rankOne, ENNReal.toReal_ofReal (energy_nonneg _ _ _ _ _ _ _ _ _)]

/-- The one-vector spectral source of a rank-one state. -/
def singleSource (u : Reference (Fin N × Fin 3) V) (w : WaveSpace (Fin N × Fin 3))
    (hw : inclusion (Fin N × Fin 3) V u = w) :
    PhysicalPFSource.Source (Fin N × Fin 3) V B
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne w) where
  vector n := if n = 0 then u else 0
  hasSum := by
    apply (hasSum_ite_eq 0 ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne w)).congr_fun
    intro n
    by_cases hn : n = 0
    · simp only [hn, if_true, hw]
    · simp only [hn, if_false, map_zero, PhysicalNormalSpectral.rankOne_zero]

theorem singleSource_zero (u : Reference (Fin N × Fin 3) V) (w : WaveSpace (Fin N × Fin 3))
    (hw : inclusion (Fin N × Fin 3) V u = w) :
    (singleSource V B u w hw).vector 0 = u := by
  change ite ((0 : ℕ) = 0) u 0 = u
  exact if_pos rfl

theorem singleSource_ne (u : Reference (Fin N × Fin 3) V) (w : WaveSpace (Fin N × Fin 3))
    (hw : inclusion (Fin N × Fin 3) V u = w) {n : ℕ} (hn : n ≠ 0) :
    (singleSource V B u w hw).vector n = 0 := by
  change ite (n = 0) u 0 = 0
  exact if_neg hn

variable {V B} in
theorem single_density_zero (u : Reference (Fin N × Fin 3) V) (w : WaveSpace (Fin N × Fin 3))
    (hw : inclusion (Fin N × Fin 3) V u = w) (j : Fin N)
    (t : RemovalConstraints.BoundedSpatialTest (volume : Measure PhysicalPairSpace.Position))
    (n : ℕ) (hn : n ≠ 0) :
    (∫ z, t.weight ((PhysicalSourceCoordinates.split j) z).1 *
        ‖inclusion (Fin N × Fin 3) V ((singleSource V B u w hw).vector n) z‖ ^ 2) = 0 := by
  have h0 : inclusion (Fin N × Fin 3) V ((singleSource V B u w hw).vector n) = 0 :=
    (congrArg (inclusion (Fin N × Fin 3) V) (singleSource_ne V B u w hw hn)).trans (map_zero _)
  apply integral_eq_zero_of_ae
  filter_upwards [Filter.EventuallyEq.of_eq (congrArg (fun f : WaveSpace (Fin N × Fin 3) => ⇑f) h0),
    Lp.coeFn_zero PhotonFock 2 (volume : Measure (PhysicalPFReference.Position (Fin N × Fin 3)))]
    with z h₁ h₂
  change _ * ‖inclusion (Fin N × Fin 3) V ((singleSource V B u w hw).vector n) z‖ ^ 2 = 0
  rw [h₁, h₂, Pi.zero_apply, norm_zero]
  simp

theorem single_current_zero (u : Reference (Fin N × Fin 3) V) (w : WaveSpace (Fin N × Fin 3))
    (hw : inclusion (Fin N × Fin 3) V u = w) (j : Fin N) (b : Fin 3)
    (t : RemovalConstraints.BoundedSpatialTest (volume : Measure PhysicalPairSpace.Position))
    (n : ℕ) (hn : n ≠ 0) :
    (∫ z, t.weight ((PhysicalSourceCoordinates.split j) z).1 *
        (⟪inclusion (Fin N × Fin 3) V ((singleSource V B u w hw).vector n) z,
          covariant (Fin N × Fin 3) V C κP hκP M hbP e (j, b)
            ((singleSource V B u w hw).vector n) z⟫_ℂ).re) = 0 := by
  have h0 : inclusion (Fin N × Fin 3) V ((singleSource V B u w hw).vector n) = 0 :=
    (congrArg (inclusion (Fin N × Fin 3) V) (singleSource_ne V B u w hw hn)).trans (map_zero _)
  apply integral_eq_zero_of_ae
  filter_upwards [Filter.EventuallyEq.of_eq (congrArg (fun f : WaveSpace (Fin N × Fin 3) => ⇑f) h0),
    Lp.coeFn_zero PhotonFock 2 (volume : Measure (PhysicalPFReference.Position (Fin N × Fin 3)))]
    with z h₁ h₂
  have hz : (inclusion (Fin N × Fin 3) V ((singleSource V B u w hw).vector n) z) = 0 :=
    h₁.trans (h₂.trans (Pi.zero_apply z))
  exact (congrArg (fun y : PhotonFock => t.weight ((PhysicalSourceCoordinates.split j) z).1 *
    (⟪y, covariant (Fin N × Fin 3) V C κP hκP M hbP e (j, b)
      ((singleSource V B u w hw).vector n) z⟫_ℂ).re) hz).trans (by simp)

theorem single_tested_density (u : Reference (Fin N × Fin 3) V) (w : WaveSpace (Fin N × Fin 3))
    (hw : inclusion (Fin N × Fin 3) V u = w)
    (he : (PhysicalPFStates.energy V C κP hκP M hbP B S e).expectation
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne w) < ⊤) (j : Fin N)
    (t : RemovalConstraints.BoundedSpatialTest (volume : Measure PhysicalPairSpace.Position)) :
    (∫ z, t.weight z * densityL1 ((singleSource V B u w hw).pair C M S e j V κP hκP hbP he) z) =
      ∫ z, t.weight z * densityL1 (PhysicalPFParticle.pair C K hK M hM V j e u) z := by
  have h₁ := (singleSource V B u w hw).pair_tested_density C M S e j V κP hκP hbP he t.weight
      t.measurable (ae_of_all _ t.bounded)
  have h₂ := PhysicalSourcePair.tested_density_ofWaveFunction j
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (j, a) u) t.weight
      t.measurable (ae_of_all _ t.bounded)
  have h₃ : (∑' n, ∫ z, t.weight ((PhysicalSourceCoordinates.split j) z).1 *
      ‖inclusion (Fin N × Fin 3) V ((singleSource V B u w hw).vector n) z‖ ^ 2) =
      ∫ z, t.weight ((PhysicalSourceCoordinates.split j) z).1 *
        ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2 :=
    (tsum_eq_single 0 fun n hn => single_density_zero u w hw j t n hn).trans
      (congrArg (fun r : Reference (Fin N × Fin 3) V => ∫ z,
        t.weight ((PhysicalSourceCoordinates.split j) z).1 *
          ‖inclusion (Fin N × Fin 3) V r z‖ ^ 2) (singleSource_zero V B u w hw))
  exact h₁.trans ((congrArg (fun r : ℝ => (N : ℝ) * r) h₃).trans h₂.symm)

theorem single_tested_current (u : Reference (Fin N × Fin 3) V) (w : WaveSpace (Fin N × Fin 3))
    (hw : inclusion (Fin N × Fin 3) V u = w)
    (he : (PhysicalPFStates.energy V C κP hκP M hbP B S e).expectation
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne w) < ⊤) (j : Fin N) (b : Fin 3)
    (t : RemovalConstraints.BoundedSpatialTest (volume : Measure PhysicalPairSpace.Position)) :
    (∫ z, t.weight z *
        currentL1 ((singleSource V B u w hw).pair C M S e j V κP hκP hbP he) z b) =
      ∫ z, t.weight z * currentL1 (PhysicalPFParticle.pair C K hK M hM V j e u) z b := by
  have h₁ := (singleSource V B u w hw).pair_tested_current C M S e j V κP hκP hbP he b t.weight
      t.measurable (ae_of_all _ t.bounded)
  have h₂ := PhysicalSourcePair.tested_current_ofWaveFunction j
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (j, a) u) b t.weight
      t.measurable (ae_of_all _ t.bounded)
  have h₃ : (∑' n, ∫ z, t.weight ((PhysicalSourceCoordinates.split j) z).1 *
      (⟪inclusion (Fin N × Fin 3) V ((singleSource V B u w hw).vector n) z,
        covariant (Fin N × Fin 3) V C κP hκP M hbP e (j, b)
          ((singleSource V B u w hw).vector n) z⟫_ℂ).re) =
      ∫ z, t.weight ((PhysicalSourceCoordinates.split j) z).1 *
        (⟪inclusion (Fin N × Fin 3) V u z,
          covariant (Fin N × Fin 3) V C κP hκP M hbP e (j, b) u z⟫_ℂ).re :=
    (tsum_eq_single 0 fun n hn => single_current_zero V C K hK M hM B e u w hw j b t n hn).trans
      (congrArg (fun r : Reference (Fin N × Fin 3) V => ∫ z,
        t.weight ((PhysicalSourceCoordinates.split j) z).1 *
          (⟪inclusion (Fin N × Fin 3) V r z,
            covariant (Fin N × Fin 3) V C κP hκP M hbP e (j, b) r z⟫_ℂ).re)
        (singleSource_zero V B u w hw))
  exact h₁.trans ((congrArg (fun r : ℝ => (N : ℝ) * r) h₃).trans h₂.symm)

/-- The pair of a rank-one state is the constructed wave-function pair. -/
theorem rankOne_pair (u : Reference (Fin N × Fin 3) V) (w : WaveSpace (Fin N × Fin 3))
    (hw : inclusion (Fin N × Fin 3) V u = w)
    (hx : (B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne w ∈
      (B.realization (WaveSpace (Fin N × Fin 3))).rank.positive)
    (he : (PhysicalPFStates.energy V C κP hκP M hbP B S e).expectation
      ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne w) < ⊤) (j : Fin N) :
    PhysicalPFStates.pair j V C κP hκP M hbP B S e _ hx he =
      PhysicalPFParticle.pair C K hK M hM V j e u :=
  (PhysicalPFStates.pair_eq_source j V C κP hκP M hbP B S e _ hx he
    (singleSource V B u w hw)).trans
    (pair_eq_of_bounded_spatial_tests _ _
      (fun t => single_tested_density V C K hK M hM B S e u w hw he j t)
      (fun b t => single_tested_current V C K hK M hM B S e u w hw he j b t))

/-- The pure-state pair is the constructed wave-function pair. -/
theorem pure_density (v : PureState V C K hK M hM B S e) (u : Reference (Fin N × Fin 3) V)
    (hu : inclusion (Fin N × Fin 3) V u = v.val) :
    (pureModel V C K hK M hM B S e i).density v =
      PhysicalPFParticle.pair C K hK M hM V i e u :=
  rankOne_pair V C K hK M hM B S e u v.val hu
    ((B.realization (WaveSpace (Fin N × Fin 3))).rank.rankOne_positive v.val) v.property.2.2 i

/-- **Generic covariance of `F_LL`.** A bijection of wave functions that
preserves norms and the fermionic subspace, lifts to the reference domain,
and transforms energy and the constructed pair by `ℓ` and `τ` gives
`F_LL(τ d) = F_LL(d) + ℓ(d)`. -/
theorem search_covariance_of_reference
    (Φ Ψ : WaveSpace (Fin N × Fin 3) → WaveSpace (Fin N × Fin 3))
    (τ : Pair ≃ Pair) (ℓ : Pair → ℝ)
    (hΦn : ∀ v, ‖Φ v‖ = ‖v‖) (hΨn : ∀ v, ‖Ψ v‖ = ‖v‖)
    (hΦf : ∀ v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock,
      Φ v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
    (hΨf : ∀ v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock,
      Ψ v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
    (hΨΦ : ∀ v, Ψ (Φ v) = v) (hΦΨ : ∀ v, Φ (Ψ v) = v)
    (hΨr : ∀ u : Reference (Fin N × Fin 3) V,
      ∃ u' : Reference (Fin N × Fin 3) V,
        inclusion (Fin N × Fin 3) V u' = Ψ (inclusion (Fin N × Fin 3) V u))
    (hT : ∀ u : Reference (Fin N × Fin 3) V,
      inclusion (Fin N × Fin 3) V u ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock →
      ∃ u' : Reference (Fin N × Fin 3) V,
        inclusion (Fin N × Fin 3) V u' = Φ (inclusion (Fin N × Fin 3) V u) ∧
        energy (Fin N × Fin 3) V C κP hκP M hbP e u' =
          energy (Fin N × Fin 3) V C κP hκP M hbP e u +
            ℓ (PhysicalPFParticle.pair C K hK M hM V i e u) ∧
        PhysicalPFParticle.pair C K hK M hM V i e u' =
          τ (PhysicalPFParticle.pair C K hK M hM V i e u))
    (d : Pair) :
    DFT.search (pureModel V C K hK M hM B S e i) (τ d) =
      DFT.search (pureModel V C K hK M hM B S e i) d + ((ℓ d : ℝ) : EReal) := by
  let ref : PureState V C K hK M hM B S e → Reference (Fin N × Fin 3) V := fun v =>
    Classical.choose (pure_reference V C K hK M hM B S e v)
  have href (v : PureState V C K hK M hM B S e) :
      inclusion (Fin N × Fin 3) V (ref v) = v.val :=
    Classical.choose_spec (pure_reference V C K hK M hM B S e v)
  have hferm (v : PureState V C K hK M hM B S e) : inclusion (Fin N × Fin 3) V (ref v) ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
    (congrArg (fun w => w ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock)
      (href v)).mpr (pure_fermionic V C K hK M hM B S e v)
  let img : PureState V C K hK M hM B S e → Reference (Fin N × Fin 3) V := fun v =>
    Classical.choose (hT (ref v) (hferm v))
  have himg (v : PureState V C K hK M hM B S e) :=
    Classical.choose_spec (hT (ref v) (hferm v))
  have himgv (v : PureState V C K hK M hM B S e) :
      inclusion (Fin N × Fin 3) V (img v) = Φ v.val :=
    (himg v).1.trans (congrArg Φ (href v))
  let toFun : PureState V C K hK M hM B S e → PureState V C K hK M hM B S e := fun v =>
    ofVector V C K hK M hM B S e (Φ v.val) ((hΦn v.val).trans v.property.1)
      (hΦf v.val (pure_fermionic V C K hK M hM B S e v)) ⟨img v, himgv v⟩
  let invFun : PureState V C K hK M hM B S e → PureState V C K hK M hM B S e := fun v =>
    ofVector V C K hK M hM B S e (Ψ v.val) ((hΨn v.val).trans v.property.1)
      (hΨf v.val (pure_fermionic V C K hK M hM B S e v))
      ((hΨr (ref v)).imp fun u' h => h.trans (congrArg Ψ (href v)))
  let T : PureState V C K hK M hM B S e ≃ PureState V C K hK M hM B S e :=
    { toFun := toFun
      invFun := invFun
      left_inv := fun v => Subtype.ext (hΨΦ v.val)
      right_inv := fun v => Subtype.ext (hΦΨ v.val) }
  refine Transformations.search_covariance (pureModel V C K hK M hM B S e i) T τ ℓ
    (fun v => ?_) (fun v => ?_) d
  · exact (pure_density V C K hK M hM B S e i (T v) (img v) (himgv v)).trans
      ((himg v).2.2.trans (congrArg τ (pure_density V C K hK M hM B S e i v (ref v)
        (href v)).symm))
  · exact (pure_energy V C K hK M hM B S e i (T v) (img v) (himgv v)).trans
      ((himg v).2.1.trans (congrArg₂ (· + ·)
        (pure_energy V C K hK M hM B S e i v (ref v) (href v)).symm
        (congrArg ℓ (pure_density V C K hK M hM B S e i v (ref v) (href v)).symm)))

end GptLean.TransformationsPureStates
