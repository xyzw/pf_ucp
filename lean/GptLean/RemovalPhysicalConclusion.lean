import GptLean.RemovalPhysicalPair
import GptLean.RemovalOptimized

/-!
One physical exact-removal conclusion contains the density, vector
current, prescribed marginal, zero soft energy and energy estimate for
one normalized finite-energy state. Scale optimization retains these
properties and any additional proved property of the same state.
-/

noncomputable section

namespace GptLean.RemovalConstraints

open MeasureTheory Filter RemovalState RemovalConstruction

variable {X T DensityTest CurrentTest Particle Direction Marginal : Type*}
  [MeasurableSpace X] {ν : Measure X}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {Tr : PositiveTraceData T} {E : PositiveForm Tr}
  [Fintype Particle] [Fintype Direction]
  {density : DensityTest → T →L[ℝ] ℝ} {current : CurrentTest → FormObservable E}

/-- All physical conclusions concern the same state `r`. Its type already
asserts positivity, trace one and finite total energy. -/
structure PhysicalRemovalConclusion
    (P : PhysicalPairData density current ν Particle Direction) (m r : E.State)
    (marginal : E.State → Marginal) (target : Marginal)
    (softForm : PositiveForm Tr) (Esoft error : ℝ) : Prop where
  density_eq : P.rho r =ᵐ[ν] P.rho m
  current_eq : P.currentDensity r =ᵐ[ν] P.currentDensity m
  marginal_eq : marginal r = target
  soft_zero : softForm.expectation r.val = 0
  energy_bound : (E.expectation r.val).toReal ≤ (E.expectation m.val).toReal - Esoft + error

namespace PhysicalPairData

variable (P : PhysicalPairData density current ν Particle Direction)

/-- Combine the physical constraints and free-scale energy estimate of
an already constructed output. No new state is selected. -/
theorem localizedOutput_conclusion
    {m : E.State} {marginal : E.State → Marginal} {target : Marginal}
    {softForm : PositiveForm Tr} {Esoft C e k L a b : ℝ}
    (out : SoftRemoval.LocalizedOutput (VectorData.model (testedPair density current)) m
      marginal target Esoft C e k L a b)
    (hzero : softForm.expectation out.state.val = 0)
    (hC : 0 ≤ C) (he : 0 ≤ e) (hk : 0 ≤ k) :
    PhysicalRemovalConclusion P m out.state marginal target softForm Esoft
      (C * RemovalEstimates.scaleError e k L b (a ^ 2 * Esoft + b ^ 2)) := by
  obtain ⟨hρ, hj⟩ := P.localizedOutput_equal out
  exact ⟨hρ, hj, out.marginal_eq, hzero, out.energy_bound hC he hk⟩

/-- The exact-output subtype used by the physical construction gives all
five conclusions for its own state. -/
theorem exactOutput_conclusion
    {m : E.State} {marginal : E.State → Marginal} {target : Marginal}
    {softForm : PositiveForm Tr} {Esoft C e k L a b : ℝ}
    (out : {out : SoftRemoval.LocalizedOutput (VectorData.model (testedPair density current)) m
      marginal target Esoft C e k L a b // softForm.expectation out.state.val = 0})
    (hC : 0 ≤ C) (he : 0 ≤ e) (hk : 0 ≤ k) :
    PhysicalRemovalConclusion P m out.val.state marginal target softForm Esoft
      (C * RemovalEstimates.scaleError e k L b (a ^ 2 * Esoft + b ^ 2)) :=
  P.localizedOutput_conclusion out.val out.property hC he hk

/-- Optimization preserves zero soft energy, both physical functions,
the prescribed marginal and an arbitrary additional state property.
Nonnegativity of the removed energy follows from the source soft series. -/
theorem optimized_output_conclusion_with_property
    (m : E.State) (marginal : E.State → Marginal) (target : Marginal)
    (softForm : PositiveForm Tr) (property : E.State → Prop)
    {Esoft C e k a b : ℝ}
    (hC : 0 ≤ C) (he : 0 ≤ e) (hk : 0 < k) (hk1 : k ≤ 1)
    (outputs : ∀ L, 1 ≤ L → k * L ≤ 1 →
      {out : SoftRemoval.LocalizedOutput (VectorData.model (testedPair density current)) m
        marginal target Esoft C e k L a b //
        softForm.expectation out.state.val = 0 ∧ property out.state}) :
    ∃ r : E.State, PhysicalRemovalConclusion P m r marginal target softForm Esoft
      ((3 * C) * SoftPurification.removalError e k a b Esoft) ∧ property r := by
  let one := outputs 1 le_rfl (by simpa using hk1)
  have hE : 0 ≤ Esoft := by
    rw [← one.val.soft_total]
    exact tsum_nonneg one.val.soft_nonneg
  obtain ⟨r, hpair, hmarginal, hproperty, henergy⟩ :=
    SoftRemoval.optimized_output_with_property m marginal target
      (fun r => softForm.expectation r.val = 0 ∧ property r) hC he hk hk1 hE outputs
  obtain ⟨hρ, hj⟩ := P.equal_of_testedPair hpair
  exact ⟨r, ⟨hρ, hj, hmarginal, hproperty.1, henergy⟩, hproperty.2⟩

/-- The optimized physical conclusion when no extra subspace or symmetry
property is requested. -/
theorem optimized_output_conclusion
    (m : E.State) (marginal : E.State → Marginal) (target : Marginal)
    (softForm : PositiveForm Tr) {Esoft C e k a b : ℝ}
    (hC : 0 ≤ C) (he : 0 ≤ e) (hk : 0 < k) (hk1 : k ≤ 1)
    (outputs : ∀ L, 1 ≤ L → k * L ≤ 1 →
      {out : SoftRemoval.LocalizedOutput (VectorData.model (testedPair density current)) m
        marginal target Esoft C e k L a b // softForm.expectation out.state.val = 0}) :
    ∃ r : E.State, PhysicalRemovalConclusion P m r marginal target softForm Esoft
      ((3 * C) * SoftPurification.removalError e k a b Esoft) := by
  obtain ⟨r, hr, _⟩ := P.optimized_output_conclusion_with_property m marginal target softForm
    (fun _ => True) hC he hk hk1
    (fun L hL hkL => ⟨(outputs L hL hkL).val, (outputs L hL hkL).property, trivial⟩)
  exact ⟨r, hr⟩

end PhysicalPairData
end GptLean.RemovalConstraints
