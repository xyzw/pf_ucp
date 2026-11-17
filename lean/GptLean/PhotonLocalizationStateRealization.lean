import GptLean.PhotonLossClosure
import GptLean.PhotonLocalizationDensity
import GptLean.PositiveForm

/-!
The physical state type as the finite-energy part of the ambient normal
state space. Realization, energy and number agreement are consequences
of this choice. Density convergence supplies the electronic tightness
predicate used by the common-channel coarse endpoint.
-/

namespace GptLean.PhotonLoss

open MeasureTheory Filter Topology
open scoped ENNReal

variable {X Test Pair : Type*} [NormedAddCommGroup X]
  [TopologicalSpace Pair]

/-- A normalized ambient state with finite PF form expectation. -/
def FiniteEnergyState (D : LocalizationData X) (T : TraceData D Test) :=
  {x : X // x ∈ D.states ∧ T.energy x < ⊤}

/-- The real energy used in the constrained search is the value of the
same finite extended-real form, without an additional energy bridge. -/
noncomputable def finiteEnergyModel
    (D : LocalizationData X) (T : TraceData D Test)
    (pair : FiniteEnergyState D T → Pair) :
    DFT.StateModel (FiniteEnergyState D T) Pair where
  energy s := (T.energy s.val).toReal
  density := pair

section FormSector

variable [NormedSpace ℝ X] [CompleteSpace X]

/-- The subtype used by photon loss is canonically the physical
positive-form state in its prescribed sector. This identifies the
exact-removal output type with the attainment state type using only the
common trace and energy realization. In the fermionic case `S` is the
fixed set of the electronic compression. -/
def FiniteEnergyState.equivFormSector
    (D : LocalizationData X) (T : TraceData D Test)
    (Tr : RemovalState.PositiveTraceData X) (E : RemovalState.PositiveForm Tr)
    (S : Set X)
    (hstates : ∀ x, x ∈ D.states ↔ x ∈ Tr.positive ∧ Tr.trace x = 1 ∧ x ∈ S)
    (henergy : ∀ x ∈ D.states, T.energy x = E.expectation x) :
    FiniteEnergyState D T ≃ {s : E.State // s.val ∈ S} where
  toFun s := ⟨⟨s.val, ((hstates s.val).mp s.property.1).1,
    ((hstates s.val).mp s.property.1).2.1,
    by simpa only [henergy s.val s.property.1] using s.property.2⟩,
      ((hstates s.val).mp s.property.1).2.2⟩
  invFun s := ⟨s.val.val,
    (hstates s.val.val).mpr ⟨s.val.property.1, s.val.property.2.1, s.property⟩,
    by simpa only [henergy s.val.val ((hstates s.val.val).mpr
      ⟨s.val.property.1, s.val.property.2.1, s.property⟩)] using s.val.property.2.2⟩
  left_inv s := Subtype.ext rfl
  right_inv s := Subtype.ext (Subtype.ext rfl)

end FormSector

/-- Constraints realized on the finite-energy ambient states. The
bounded tests and density component are universal physical observable
identities. All state-realization obligations are proved here.

The identity `htight` makes explicit the density-convergence predicate
produced by `CoarseData.ofChannelSources`. It is not a compactness or
limiting-state assumption. -/
noncomputable def ConstraintRealization.ofFiniteEnergyStates
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (D : LocalizationData X) (T : TraceData D Test)
    (J : LocalizationEstimates D T)
    (pair : FiniteEnergyState D T → Pair)
    (pairTest : Test → Pair → ℝ)
    (hcontinuous : ∀ t, Continuous (pairTest t))
    (hseparates : ∀ d d', (∀ t, pairTest t d = pairTest t d') → d = d')
    (htest : ∀ t s, T.test t s.val = pairTest t (pair s))
    (density : X → Lp ℝ 1 μ)
    (densityComponent : Pair → Lp ℝ 1 μ)
    (hcomponent : Continuous densityComponent)
    (hdensity : ∀ s, density s.val = densityComponent (pair s))
    (htight : J.electronicTight = fun u =>
      ∃ ρ, Tendsto (fun n => density (u n)) atTop (𝓝 ρ)) :
    ConstraintRealization J (finiteEnergyModel D T pair)
      (fun s => T.number s.val) where
  repr s := s.val
  repr_mem s := s.property.1
  energy_nonneg s := ENNReal.toReal_nonneg
  energy_repr s := (ENNReal.ofReal_toReal s.property.2.ne).symm
  number_repr _ := rfl
  realize x hx hfinite := ⟨⟨x, hx, hfinite⟩, rfl⟩
  pairTest := pairTest
  pairTest_cont := hcontinuous
  pairTest_separates := hseparates
  test_repr := htest
  tight_of_converges s d hs := by
    rw [htight]
    refine ⟨densityComponent d, ?_⟩
    have hc := (hcomponent.tendsto d).comp hs
    simpa only [Function.comp_def, finiteEnergyModel, hdensity] using hc

end GptLean.PhotonLoss
