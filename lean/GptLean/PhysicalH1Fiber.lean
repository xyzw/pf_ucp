import GptLean.PhysicalKineticForm
import GptLean.PhysicalL2FiberSum
import GptLean.ElectronicH1Map

/-!
Scalar fiber coefficients describe the actual Hilbert-valued weak H1
space. Parseval gives the sum of their kinetic energies. Conversely,
summable scalar derivative energies reconstruct an H1 vector by finite
fiber sums and closedness of the distributional derivative graph.
-/

noncomputable section

namespace GptLean.PhysicalH1Fiber

open MeasureTheory Filter Topology ElectronicH1Complex PhysicalL2HilbertSum PhysicalL2FiberSum
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

variable {H I ι : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedSpace ℝ H]
  [IsScalarTower ℝ ℂ H] [CompleteSpace H]
  (b : HilbertBasis ι ℂ H)

def coefficient (a : ι) : ComplexH1 H I →L[ℂ] ComplexH1 ℂ I :=
  ElectronicH1Map.map (innerSL ℂ (b a))

theorem value_coefficient (u : ComplexH1 H I) (a : ι) :
    value (coefficient b a u) = fiberCoefficients b (value u) a :=
  (fiberCoefficients_apply b (value u) a).symm

theorem derivative_coefficient (u : ComplexH1 H I) (a : ι) (j : I) :
    derivative j (coefficient b a u) = fiberCoefficients b (derivative j u) a :=
  (fiberCoefficients_apply b (derivative j u) a).symm

omit [DecidableEq I] [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H] in
theorem coefficient_norm_sq_hasSum (u : ElectronicH1Space.L2 H I) :
    HasSum (fun a => ‖fiberCoefficients b u a‖ ^ 2) (‖u‖ ^ 2) := by
  have h := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (fiberCoefficients b u)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, (fiberCoefficients b).norm_map] using h

theorem kinetic_hasSum (u : ComplexH1 H I) :
    HasSum (fun a => ∑ j : I, ‖derivative j (coefficient b a u)‖ ^ 2)
      (∑ j : I, ‖derivative j u‖ ^ 2) := by
  simpa only [derivative_coefficient] using
    (hasSum_sum (s := Finset.univ) (fun j _ => coefficient_norm_sq_hasSum b (derivative j u)))

private def tensorH1 (v : H) : ComplexH1 ℂ I →L[ℂ] ComplexH1 H I :=
  ElectronicH1Map.map ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).flip v)

private theorem value_tensorH1 (v : H) (u : ComplexH1 ℂ I) :
    value (tensorH1 v u) = tensor (value u) v := rfl

private theorem derivative_tensorH1 (v : H) (u : ComplexH1 ℂ I) (j : I) :
    derivative j (tensorH1 v u) = tensor (derivative j u) v := rfl

/-- Scalar H1 coefficients with summable kinetic energies reconstruct the
actual vector weak H1 domain. -/
theorem exists_h1_of_coefficients (u : ElectronicH1Space.L2 H I)
    (g : ι → ComplexH1 ℂ I)
    (hvalue : ∀ a, value (g a) = fiberCoefficients b u a)
    (henergy : Summable (fun a => ∑ j : I, ‖derivative j (g a)‖ ^ 2)) :
    ∃ q : ComplexH1 H I, value q = u := by
  classical
  have hs (j : I) : Summable (fun a => ‖derivative j (g a)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun a => Finset.single_le_sum (fun k _ => sq_nonneg ‖derivative k (g a)‖)
        (Finset.mem_univ j)) henergy
  let ds (j : I) : lp (fun _ : ι => ElectronicH1Space.L2 ℂ I) 2 :=
    ⟨fun a => derivative j (g a), memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs j)⟩
  let d (j : I) : ElectronicH1Space.L2 H I := (fiberCoefficients b).symm (ds j)
  have hd (j : I) : HasSum (fun a => tensor (derivative j (g a)) (b a)) (d j) := by
    have h := hasSum_tensor_fiberCoefficients b (d j)
    have heq (a : ι) : fiberCoefficients b (d j) a = derivative j (g a) := by
      change fiberCoefficients b ((fiberCoefficients b).symm (ds j)) a = _
      rw [LinearIsometryEquiv.apply_symm_apply]
    simpa only [heq] using h
  let q (s : Finset ι) : ComplexH1 H I := ∑ a ∈ s, tensorH1 (b a) (g a)
  have hv : Tendsto (fun s : Finset ι => value (q s)) atTop (𝓝 u) := by
    have h := hasSum_tensor_fiberCoefficients b u
    simpa only [HasSum, SummationFilter.unconditional_filter, q, map_sum, value_tensorH1, hvalue] using h
  have hdconv : Tendsto (fun s : Finset ι => fun j : I => derivative j (q s)) atTop (𝓝 d) := by
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [HasSum, SummationFilter.unconditional_filter, q, map_sum, derivative_tensorH1] using hd j
  have hclosed : (u, d) ∈ complexWeakGraph H I :=
    isClosed_complexWeakGraph.mem_of_tendsto (hv.prodMk_nhds hdconv)
      (Eventually.of_forall fun s => (q s).property)
  exact ⟨⟨(u, d), hclosed⟩, rfl⟩

end GptLean.PhysicalH1Fiber
