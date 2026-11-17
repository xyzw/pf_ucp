import GptLean.PhysicalRelativeCoordinates
import GptLean.PhysicalCoulombIntegrability
import GptLean.PhysicalMultiplicationGraph
import GptLean.ElectronicH1Complex
import GptLean.SymmetricLift.PairEnergyIntegrability

/-!
Every actual electronic H1 vector lies in the repulsive Coulomb form
domain. Relative-coordinate Fubini and the actual H1 Sobolev theorem
prove each pair interaction finite. Their finite sum constructs the
square-root multiplication graph used by the physical PF reference.
-/

noncomputable section

namespace GptLean.PhysicalCoulombH1

open MeasureTheory GptLean.SymmetricLift GptLean.ElectronicH1Space
open GptLean.PhysicalRelativeCoordinates GptLean.PhysicalSourceMarginal
open GptLean.PhysicalSourceFubini GptLean.PhysicalCoulombIntegrability
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem pair_coulomb_integrable (i j : Fin N) (hij : i ≠ j)
    (u : H1 H (Fin N × Fin 3)) :
    Integrable (fun x => ‖particle x i - particle x j‖⁻¹ * ‖value u x‖ ^ 2) volume := by
  let e := relativeSplit i j hij
  let he := relativeSplit_symm_measurePreserving i j hij
  have h₆ : MemLp (curry (productMap e he (value u))) 6 volume :=
    relativeSource_memLp_six i j hij u
  have hi := product_coulomb_integrable (productMap e he (value u)) h₆
  have hc : Integrable (fun p => ‖(e (e.symm p)).1‖⁻¹ * ‖value u (e.symm p)‖ ^ 2)
      (volume.prod volume) := by
    apply hi.congr
    filter_upwards [Lp.coeFn_compMeasurePreserving (value u) he] with p hp
    change ‖p.1‖⁻¹ * ‖Lp.compMeasurePreserving e.symm he (value u) p‖ ^ 2 = _
    change Lp.compMeasurePreserving e.symm he (value u) p = value u (e.symm p) at hp
    rw [hp, ContinuousLinearEquiv.apply_symm_apply]
  have hf := (he.integrable_comp_emb
    (g := fun x => ‖(e x).1‖⁻¹ * ‖value u x‖ ^ 2)
    e.symm.toHomeomorph.measurableEmbedding).mp hc
  simpa only [e, relativeSplit_fst] using hf

def potential (N : ℕ) (x : Configuration N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if i < j then ‖particle x i - particle x j‖⁻¹ else 0

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] in
theorem potential_nonneg (N : ℕ) (x : Configuration N) : 0 ≤ potential N x := by
  unfold potential
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] in
theorem potential_measurable (N : ℕ) : Measurable (potential N) := by
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    exact (pairDifferenceLinear i j).continuous_of_finiteDimensional.measurable.norm.inv
  · simp only [ite_eq_right hij]
    exact measurable_const

theorem potential_integrable (u : H1 H (Fin N × Fin 3)) :
    Integrable (fun x => potential N x * ‖value u x‖ ^ 2) volume := by
  simp only [potential, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  by_cases hij : i < j
  · simpa only [ite_eq_left hij] using pair_coulomb_integrable i j (ne_of_lt hij) u
  · simp only [ite_eq_right hij, zero_mul]
    exact integrable_zero _ _ _

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem sqrt_mul_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (V : X → ℝ) (hV : Measurable V) (hpos : ∀ x, 0 ≤ V x)
    (u : Lp H 2 μ) (hi : Integrable (fun x => V x * ‖u x‖ ^ 2) μ) :
    MemLp (fun x => (Real.sqrt (V x) : ℂ) • u x) 2 μ := by
  have hm : AEStronglyMeasurable (fun x => (Real.sqrt (V x) : ℂ) • u x) μ :=
    (Complex.measurable_ofReal.comp hV.sqrt).aestronglyMeasurable.smul (Lp.aestronglyMeasurable u)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply hi.congr
  filter_upwards [] with x
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hpos x)]

theorem scaled_potential_integrable (c : ℝ) (u : H1 H (Fin N × Fin 3)) :
    Integrable (fun x => (c * potential N x) * ‖value u x‖ ^ 2) volume := by
  simpa only [mul_assoc] using (potential_integrable u).const_mul c

theorem sqrt_potential_memLp (c : ℝ) (hc : 0 ≤ c) (u : H1 H (Fin N × Fin 3)) :
    MemLp (fun x => (Real.sqrt (c * potential N x) : ℂ) • value u x) 2 volume :=
  sqrt_mul_memLp _ (measurable_const.mul (potential_measurable N))
    (fun x => mul_nonneg hc (potential_nonneg N x)) (value u) (scaled_potential_integrable c u)

/-- The Coulomb form output is constructed from the H1 vector itself. -/
def potentialVector (c : ℝ) (hc : 0 ≤ c) (u : H1 H (Fin N × Fin 3)) : L2 H (Fin N × Fin 3) :=
  (sqrt_potential_memLp c hc u).toLp
    (fun x => (Real.sqrt (c * potential N x) : ℂ) • value u x)

def potentialGraph (c : ℝ) (hc : 0 ≤ c) (u : H1 H (Fin N × Fin 3)) :
    PhysicalMultiplicationGraph.GraphSpace volume (H := H)
      (fun x : Configuration N => (Real.sqrt (c * potential N x) : ℂ)) :=
  ⟨(value u, potentialVector c hc u), (sqrt_potential_memLp c hc u).coeFn_toLp⟩

@[simp] theorem inclusion_potentialGraph (c : ℝ) (hc : 0 ≤ c)
    (u : H1 H (Fin N × Fin 3)) :
    PhysicalMultiplicationGraph.inclusion volume _ (potentialGraph c hc u) = value u := rfl

def complexPotentialGraph (c : ℝ) (hc : 0 ≤ c)
    (u : ElectronicH1Complex.ComplexH1 H (Fin N × Fin 3)) :
    PhysicalMultiplicationGraph.GraphSpace volume (H := H)
      (fun x : Configuration N => (Real.sqrt (c * potential N x) : ℂ)) :=
  potentialGraph c hc (ElectronicH1Complex.realEquiv u)

@[simp] theorem inclusion_complexPotentialGraph (c : ℝ) (hc : 0 ≤ c)
    (u : ElectronicH1Complex.ComplexH1 H (Fin N × Fin 3)) :
    PhysicalMultiplicationGraph.inclusion volume _ (complexPotentialGraph c hc u) =
      ElectronicH1Complex.value u := rfl

end GptLean.PhysicalCoulombH1
