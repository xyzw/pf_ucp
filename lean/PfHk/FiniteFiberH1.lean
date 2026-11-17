import PfHk.FiniteFiberL2
import GptLean.ElectronicH1Map

/-! The finite Hilbert sum of electronic H1 vectors is an actual
Hilbert-valued weak H1 vector, with the prescribed coordinate derivatives. -/

noncomputable section
namespace PfHk.FiniteFiberH1

open MeasureTheory GptLean.ElectronicH1Complex

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000

variable {S H I : Type*} [Fintype S] [DecidableEq S]
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev Fiber := PiLp 2 (fun _ : S => H)

def single (s : S) : H →L[ℂ] Fiber (S := S) (H := H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : S => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : S => H) s)

omit [Fintype S] [CompleteSpace H] in
@[simp] theorem single_apply (s t : S) (z : H) :
    single s z t = if t = s then z else 0 := by
  change (Pi.single s z : S → H) t = _
  simp [Pi.single_apply]

attribute [local irreducible] single

omit [CompleteSpace H] in
theorem bundle_eq_sum_single {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : S → Lp H 2 μ) :
    FiniteFiberL2.bundle u = ∑ s, (single (S := S) (H := H) s).compLpL 2 μ (u s) := by
  apply Lp.ext
  filter_upwards [FiniteFiberL2.bundle_ae u,
    Lp.coeFn_finsetSum Finset.univ (fun s => (single (S := S) (H := H) s).compLpL 2 μ (u s)),
    ae_all_iff.mpr (fun (s : S) => (single (S := S) (H := H) s).coeFn_compLpL (u s))] with x hb hs hc
  rw [hb, hs]
  apply PiLp.ext
  intro t
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp [hc]

def bundle (u : S → ComplexH1 H I) : ComplexH1 (Fiber (S := S) (H := H)) I :=
  ∑ s, GptLean.ElectronicH1Map.map (single s) (u s)

theorem value_bundle (u : S → ComplexH1 H I) :
    value (bundle u) = FiniteFiberL2.bundle (fun s => value (u s)) := by
  simp only [bundle, map_sum, GptLean.ElectronicH1Map.value_map]
  exact (bundle_eq_sum_single _).symm

theorem derivative_bundle (u : S → ComplexH1 H I) (i : I) :
    derivative i (bundle u) = FiniteFiberL2.bundle (fun s => derivative i (u s)) := by
  simp only [bundle, map_sum, GptLean.ElectronicH1Map.derivative_map]
  exact (bundle_eq_sum_single _).symm

theorem value_norm_sq (u : S → ComplexH1 H I) :
    ‖value (bundle u)‖ ^ 2 = ∑ s, ‖value (u s)‖ ^ 2 := by
  rw [value_bundle, FiniteFiberL2.norm_sq]

theorem derivative_norm_sq (u : S → ComplexH1 H I) (i : I) :
    ‖derivative i (bundle u)‖ ^ 2 = ∑ s, ‖derivative i (u s)‖ ^ 2 := by
  rw [derivative_bundle, FiniteFiberL2.norm_sq]

theorem bundle_injective : Function.Injective (bundle (S := S) (H := H) (I := I)) := by
  intro u v huv
  have h := congrArg value huv
  rw [value_bundle, value_bundle] at h
  have hc := FiniteFiberL2.bundle_injective h
  funext s
  exact value_injective (congrFun hc s)

end PfHk.FiniteFiberH1
