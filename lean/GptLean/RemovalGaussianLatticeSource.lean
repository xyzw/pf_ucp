import GptLean.RemovalGaussianChannel
import GptLean.RemovalSourceLatticeRepresentatives

/-!
The Gaussian moment source is the actual localized original spectral
vector. A universal radiation graph locality law transports the original
soft-energy graph through bounded electron multipliers. Consequently no
localized domain, norm or conditional mass hypotheses are required.
-/

noncomputable section

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open MeasureTheory ElectronicLocalization SymmetricLift Filter Gaussian RemovalEnergy

section RadiationLocality

variable {X H : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A radiation graph acts only on radiation variables and hence commutes
with arbitrary bounded measurable electron multiplication. -/
def SpatialRadiationLocality (domain : Lp H 2 ν → Prop)
    (radiation : Lp H 2 ν → Lp H 2 ν) : Prop :=
  ∀ (g : X → ℝ) (hg : AEStronglyMeasurable g ν) (C : ℝ) (hb : ∀ x, |g x| ≤ C)
    (u : Lp H 2 ν), domain u →
    domain (boundedRealProduct g hg C hb u) ∧
      radiation (boundedRealProduct g hg C hb u) =
        boundedRealProduct g hg C hb (radiation u)

theorem localizedVector_eq_boundedRealProduct (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (u : Lp H 2 ν) (n : ℕ) :
    localizedVector f hpart hf u n =
      boundedRealProduct (f n) (hf n) 1 (partition_abs_le_one f hpart n) u := by
  apply Lp.ext
  exact (localized_memLp f hpart hf u n).coeFn_toLp.trans
    (boundedRealProduct_memLp (f n) (hf n) 1 (partition_abs_le_one f hpart n) u).coeFn_toLp.symm

theorem SpatialRadiationLocality.localized
    {domain : Lp H 2 ν → Prop} {radiation : Lp H 2 ν → Lp H 2 ν}
    (h : SpatialRadiationLocality domain radiation)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (u : Lp H 2 ν) (hu : domain u) (n : ℕ) :
    domain (localizedVector f hpart hf u n) ∧
      radiation (localizedVector f hpart hf u n) = localizedVector f hpart hf (radiation u) n := by
  simp only [localizedVector_eq_boundedRealProduct]
  exact h (f n) (hf n) 1 (partition_abs_le_one f hpart n) u hu

end RadiationLocality
end GptLean.RemovalSource

namespace GptLean.RemovalEnergy

open MeasureTheory Filter Gaussian RemovalSource SymmetricLift ElectronicLocalization

variable {Q G Ω H K Hr Kr : Type*} [MeasurableSpace Q] [MeasurableSpace Ω]
  {μ : Measure Q} {ν : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
  {N : ℕ}

/-- The conditional Gaussian source follows from the original radiation
graph, its universal spatial locality and the ordinary WIS/Fubini maps. -/
def GaussianSourceData.ofLattice
    (src : LatticeSourceData N μ H K Hr Kr H)
    (W : WienerSegalData Q (Lp H 2 (volume : Measure (Configuration N)))
      (Lp K 2 (volume : Measure (Configuration N))) G μ)
    {weight : Ω → ℝ} (D : KernelFieldData ν W weight)
    (Fubini : Lp K 2 (μ.prod (volume : Measure (Configuration N))) ≃ₗᵢ[ℂ]
      Lp (Lp K 2 (volume : Measure (Configuration N))) 2 μ)
    (hrep : ∀ v : Lp K 2 (μ.prod (volume : Measure (Configuration N))), ∀ᵐ q ∂μ,
      (fun x => v (q, x)) =ᵐ[volume] (fun x => Fubini v q x))
    (hW : ∀ v, W.toFiber v =ᵐ[μ] (fun q => Fubini (src.U v) q))
    (locality : SpatialRadiationLocality D.radiationDomain D.radiation)
    (hdom : ∀ n, D.radiationDomain (src.ψ n))
    (hrad : ∀ n, D.radiation (src.ψ n) = src.soft n)
    (R : ℝ) (hR : 0 < R) : GaussianSourceData (src.conditioned R hR) W D := by
  let u (n : ℕ) := localizedVector (latticeMultiplier R) (latticeMultiplier_partition R)
    (latticeMultiplier_measurable R) (src.ψ (Nat.unpair n).1) (Nat.unpair n).2
  have hgraph (n : ℕ) : D.radiationDomain (u n) ∧ D.radiation (u n) =
      localizedVector (latticeMultiplier R) (latticeMultiplier_partition R)
        (latticeMultiplier_measurable R) (src.soft (Nat.unpair n).1) (Nat.unpair n).2 := by
    simpa only [hrad] using locality.localized (latticeMultiplier R)
      (latticeMultiplier_partition R) (latticeMultiplier_measurable R)
      (src.ψ (Nat.unpair n).1) (hdom _) (Nat.unpair n).2
  refine {
    vector := u
    domain := fun n => (hgraph n).1
    norm := ?_
    soft := ?_
    mass := ?_
  }
  · intro n
    rw [src.source_eq_U_localized R hR n, src.U.norm_map]
  · intro n
    rw [(hgraph n).2]
    rfl
  · intro n
    filter_upwards [product_sourceMass_fubini Fubini hrep ((src.conditioned R hR).source n),
      hW (u n)] with q hq hw
    rw [src.source_eq_U_localized R hR n] at hq
    exact hq.trans (congrArg (fun z => ‖z‖ ^ 2) hw.symm)

end GptLean.RemovalEnergy
