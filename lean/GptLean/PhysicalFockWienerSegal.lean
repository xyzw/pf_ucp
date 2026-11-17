import GptLean.PhysicalFockRealStructure
import GptLean.PhysicalFockFieldGraph
import GptLean.PhysicalFockHardSoftVacuum
import GptLean.Gaussian.CovariantSlicing

/-!
The explicitly allowed universal Wiener–Itô–Segal theorem, stated on the
constructed symmetric L² Fock model. Its unbounded operator is the ordinary
Segal graph fixed by actual creation and annihilation sectors.

The background is uniform in the one-photon measure, closed complex
subspace and conjugation. It contains no physical cutoff, spatial field,
electronic variable, normal state, energy or removal estimate. The physical
real structure, orthogonal split and their operator matching must be proved
separately. The scalar Gaussian realization is a standard theorem parameter.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

/-- A separable probability space for a scalar Gaussian realization. -/
structure GaussianProbabilitySpace where
  Q : Type
  [measurableSpace : MeasurableSpace Q]
  measure : Measure Q
  [probability : IsProbabilityMeasure measure]
  [separable : IsSeparable measure]

attribute [instance] GaussianProbabilitySpace.measurableSpace
  GaussianProbabilitySpace.probability GaussianProbabilitySpace.separable

variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (V : Submodule ℂ (Lp ℂ 2 μ)) (J : RealStructure V)

/-- Scalar WIS for the ordinary closed real one-photon space. Multiplication
is asserted only for pairs in the concrete unbounded field graph. -/
structure ScalarWienerSegal where
  space : GaussianProbabilitySpace
  unitary : generatedSubspace μ V ≃ₗᵢ[ℂ] Lp ℂ 2 space.measure
  firstChaos : J.fixedSpace →ₗᵢ[ℝ] Lp ℝ 2 space.measure
  vacuum : unitary (generatedVacuum μ V) =ᵐ[space.measure] fun _ => (1 : ℂ)
  intertwining : ∀ (g : J.fixedSpace) (u v : generatedSubspace μ V),
    SegalGraph μ ((g : V) : Lp ℂ 2 μ) u.val v.val →
      unitary v =ᵐ[space.measure] fun q => firstChaos g q • unitary u q

/-- The standard WIS theorem is universal in the concrete one-photon model.
It does not supply any physical matching assertion. -/
structure StandardWienerSegal : Prop where
  realization : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [SigmaFinite μ] [IsSeparable μ] (V : Submodule ℂ (Lp ℂ 2 μ)),
    IsClosed (V : Set (Lp ℂ 2 μ)) → ∀ J : RealStructure V,
      Nonempty (ScalarWienerSegal μ V J)

namespace ScalarWienerSegal

variable {μ V J} (W : ScalarWienerSegal μ V J)

/-- The domain is the actual restricted Segal graph domain. -/
def fieldDomain (_W : ScalarWienerSegal μ V J) (g : J.fixedSpace) (u : generatedSubspace μ V) : Prop :=
  ∃ v : generatedSubspace μ V, SegalGraph μ ((g : V) : Lp ℂ 2 μ) u.val v.val

/-- The graph has a unique value on its domain. The arbitrary off-domain
value is never used in the multiplication identity. -/
def field (g : J.fixedSpace) (u : generatedSubspace μ V) : generatedSubspace μ V := by
  classical
  exact if h : W.fieldDomain g u then Classical.choose h else 0

theorem field_graph (g : J.fixedSpace) (u : generatedSubspace μ V)
    (hu : W.fieldDomain g u) :
    SegalGraph μ ((g : V) : Lp ℂ 2 μ) u.val (W.field g u).val := by
  rw [field, dite_eq_left hu]
  exact Classical.choose_spec hu

theorem field_eq_of_graph (g : J.fixedSpace) (u v : generatedSubspace μ V)
    (h : SegalGraph μ ((g : V) : Lp ℂ 2 μ) u.val v.val) : W.field g u = v := by
  apply Subtype.ext
  exact segalGraph_unique μ _ (W.field_graph g u ⟨v, h⟩) h

/-- The generic Gaussian interface is obtained from the actual scalar
unitary and ordinary field graph. -/
def wienerSegalData : Gaussian.WienerSegalData W.space.Q
    (generatedSubspace μ V) ℂ J.fixedSpace W.space.measure :=
  Gaussian.WienerSegalData.ofUnitary W.unitary W.fieldDomain W.field
    (fun g q => W.firstChaos g q)
    (by
      intro g u hu
      simpa only [Gaussian.unitaryFiber] using
        W.intertwining g u (W.field g u) (W.field_graph g u hu))

theorem firstChaos_norm (g : J.fixedSpace) : ‖W.firstChaos g‖ = ‖g‖ :=
  W.firstChaos.norm_map g

theorem firstChaos_add_ae (g h : J.fixedSpace) :
    W.firstChaos (g + h) =ᵐ[W.space.measure]
      fun q => W.firstChaos g q + W.firstChaos h q := by
  rw [map_add]
  exact Lp.coeFn_add _ _

end ScalarWienerSegal
end GptLean.PhysicalFock
