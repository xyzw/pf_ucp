import GptLean.PhysicalWeylIntegral
import GptLean.PhysicalWeylRadiation
import GptLean.PhysicalFockSeparable
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
The Weyl integral preserves the actual radiation form domain. Strong
measurability in graph norm follows from the measurable inverse of the
injective graph inclusion. The graph-norm estimate then makes the Weyl
integral an ordinary Bochner integral in a complete space.
-/

noncomputable section

namespace GptLean.PhysicalWeyl

open MeasureTheory Filter PhysicalFock Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 800000

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

private theorem graphInclusion_injective : Function.Injective radiationGraphInclusion := by
  intro u v h
  have hz : (u - v).val.1 = 0 := sub_eq_zero.mpr h
  have ho := radiationRoot.graph_fst_eq_zero_snd (u - v).property hz
  apply Subtype.ext
  exact Prod.ext h (sub_eq_zero.mp ho)

/-- Measurability in the closed radiation graph follows from measurability
of the underlying Fock vectors. -/
theorem radiationGraph_aestronglyMeasurable {q : X → RadiationGraphSpace}
    (hq : AEStronglyMeasurable (fun x => radiationGraphInclusion (q x)) ν) :
    AEStronglyMeasurable q ν := by
  let : MeasurableSpace PhotonFock := borel PhotonFock
  let : BorelSpace PhotonFock := ⟨rfl⟩
  let : MeasurableSpace RadiationGraphSpace := borel RadiationGraphSpace
  let : BorelSpace RadiationGraphSpace := ⟨rfl⟩
  have he := radiationGraphInclusion.continuous.measurableEmbedding graphInclusion_injective
  exact (he.aemeasurable_comp_iff.mp hq.aemeasurable).aestronglyMeasurable

variable (W : ConcreteWeylLaw photonMeasure)
  (f : X → Lp ℂ 2 photonMeasure) (hf : AEStronglyMeasurable f ν)
  (K : X → WeightedPhotonKernel)
  (hK : ∀ x, ∀ᵐ p ∂photonMeasure,
    (K x).val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f x p)

include hf in
theorem weylGraph_aestronglyMeasurable (q : RadiationGraphSpace) :
    AEStronglyMeasurable (fun x => weylGraph W (K x) (hK x) q) ν := by
  apply radiationGraph_aestronglyMeasurable
  exact W.continuous.comp_aestronglyMeasurable (hf.prodMk aestronglyMeasurable_const)

variable (a : X → ℂ) (ha : Integrable a ν)
  (hKa : Integrable (fun x => ‖a x‖ * ‖(K x).val.2‖) ν)

include hf ha hKa in
theorem weighted_weylGraph_integrable (q : RadiationGraphSpace) :
    Integrable (fun x => a x • weylGraph W (K x) (hK x) q) ν := by
  have hm : AEStronglyMeasurable (fun x => a x • weylGraph W (K x) (hK x) q) ν :=
    ha.aestronglyMeasurable.smul (weylGraph_aestronglyMeasurable W f hf K hK q)
  apply ((ha.norm.add hKa).mul_const ‖q‖).mono' hm
  exact ae_of_all _ fun x => by
    change ‖a x • weylGraph W (K x) (hK x) q‖ ≤
      (‖a x‖ + ‖a x‖ * ‖(K x).val.2‖) * ‖q‖
    rw [norm_smul]
    calc ‖a x‖ * ‖weylGraph W (K x) (hK x) q‖
        ≤ ‖a x‖ * ((1 + ‖(K x).val.2‖) * ‖q‖) :=
          mul_le_mul_of_nonneg_left (weylGraphFun_norm_le W (K x) (hK x) q) (norm_nonneg _)
      _ = (‖a x‖ + ‖a x‖ * ‖(K x).val.2‖) * ‖q‖ := by ring

/-- The actual radiation-graph lift of the Weyl integral. -/
def weylIntegralGraph : RadiationGraphSpace →L[ℂ] RadiationGraphSpace :=
  LinearMap.mkContinuous
    { toFun := fun q => ∫ x, a x • weylGraph W (K x) (hK x) q ∂ν
      map_add' := by
        intro q r
        simp only [map_add, smul_add]
        exact integral_add (weighted_weylGraph_integrable W f hf K hK a ha hKa q)
          (weighted_weylGraph_integrable W f hf K hK a ha hKa r)
      map_smul' := by
        intro c q
        simp only [map_smul, smul_comm (a _) c]
        exact integral_smul c _ }
    (∫ x, ‖a x‖ + ‖a x‖ * ‖(K x).val.2‖ ∂ν) (by
      intro q
      calc ‖∫ x, a x • weylGraph W (K x) (hK x) q ∂ν‖
          ≤ ∫ x, (‖a x‖ + ‖a x‖ * ‖(K x).val.2‖) * ‖q‖ ∂ν := by
            apply norm_integral_le_of_norm_le ((ha.norm.add hKa).mul_const ‖q‖)
            exact ae_of_all _ fun x => by
              change ‖a x • weylGraph W (K x) (hK x) q‖ ≤
                (‖a x‖ + ‖a x‖ * ‖(K x).val.2‖) * ‖q‖
              rw [norm_smul]
              calc ‖a x‖ * ‖weylGraph W (K x) (hK x) q‖
                  ≤ ‖a x‖ * ((1 + ‖(K x).val.2‖) * ‖q‖) :=
                    mul_le_mul_of_nonneg_left
                      (weylGraphFun_norm_le W (K x) (hK x) q) (norm_nonneg _)
                _ = _ := by ring
        _ = _ := integral_mul_const _ _)

/-- The graph integral and the Fock integral are the same operator under
the concrete graph inclusion. -/
theorem weylIntegralGraph_inclusion (q : RadiationGraphSpace) :
    radiationGraphInclusion (weylIntegralGraph W f hf K hK a ha hKa q) =
      weylIntegral W f hf a ha (radiationGraphInclusion q) := by
  change radiationGraphInclusion (∫ x, a x • weylGraph W (K x) (hK x) q ∂ν) = _
  rw [← radiationGraphInclusion.integral_comp_comm
    (weighted_weylGraph_integrable W f hf K hK a ha hKa q)]
  simp only [map_smul, weylGraph_inclusion, weylIntegral_apply]

/-- The integrated operator preserves every actual field with zero real
pairing against its displacement directions. -/
theorem kernelField_weylIntegralGraph (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (hreal : ∀ᵐ x ∂ν, (⟪k.val.1, f x⟫_ℂ).re = 0)
    (q : RadiationGraphSpace) :
    kernelField C k (weylIntegralGraph W f hf K hK a ha hKa q) =
      weylIntegral W f hf a ha (kernelField C k q) := by
  apply segalGraph_unique photonMeasure k.val.1
    (kernelField_segalGraph C k (weylIntegralGraph W f hf K hK a ha hKa q))
  rw [weylIntegralGraph_inclusion]
  exact segalGraph_weylIntegral W f hf a ha k.val.1 hreal (kernelField_segalGraph C k q)

/-- The annihilation commutator of the graph lift is the explicit Weyl
integral obtained before passing to the radiation form domain. -/
theorem kernelAnnihilation_weylIntegralGraph (k : WeightedPhotonKernel)
    (hak : Integrable (fun x => a x * ⟪k.val.1, f x⟫_ℂ) ν)
    (q : RadiationGraphSpace) :
    kernelAnnihilation k (weylIntegralGraph W f hf K hK a ha hKa q) =
      weylIntegral W f hf a ha (kernelAnnihilation k q) +
        weylIntegral W f hf (fun x => a x * ⟪k.val.1, f x⟫_ℂ) hak
          (radiationGraphInclusion q) := by
  have h := annihilationGraph_weylIntegral W f hf a ha k.val.1 hak
    (show AnnihilationGraph photonMeasure k.val.1 (radiationGraphInclusion q)
      (kernelAnnihilation k q) from fun _ => rfl)
  rw [← weylIntegralGraph_inclusion W f hf K hK a ha hKa q] at h
  exact AnnihilationGraph.unique photonMeasure
    (show AnnihilationGraph photonMeasure k.val.1
      (radiationGraphInclusion (weylIntegralGraph W f hf K hK a ha hKa q))
      (kernelAnnihilation k (weylIntegralGraph W f hf K hK a ha hKa q)) from fun _ => rfl) h

end GptLean.PhysicalWeyl
