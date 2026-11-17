import GptLean.TransformationsGaugeWeakConfiguration
import GptLean.TransformationsGaugeWeakSources

/-! The article's full L3 + Linfinity gauge class acts on every actual
many-electron H1 vector, with the exact weak product rule and inverse. -/

noncomputable section

namespace GptLean.TransformationsGauge.WeakSpatialGauge

open MeasureTheory Filter SymmetricLift Repair TransformationsPhase
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable (G : WeakSpatialGauge)

def neg : WeakSpatialGauge where
  fn := -G.fn
  locallyIntegrable := G.locallyIntegrable.neg
  gradient a := -G.gradient a
  gradient_in_sum a := by
    obtain ⟨l, b, hl, hb, he⟩ := G.gradient_in_sum a
    refine ⟨-l, -b, hl.neg, hb.neg, ?_⟩
    filter_upwards [he] with x hx
    simp only [Pi.neg_apply, hx, neg_add]
  weak a φ hφ hs := by
    simpa only [Pi.neg_apply, mul_neg, integral_neg, neg_neg] using
      congrArg Neg.neg (G.weak a φ hφ hs)

@[simp] theorem neg_gradient (a : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    G.neg.gradient a x = -G.gradient a x := rfl

theorem configurationAngle_neg (N : ℕ) :
    G.neg.configurationAngle N = -G.configurationAngle N := by
  funext x
  simp only [configurationAngle, neg, Pi.neg_apply, Finset.sum_neg_distrib]

theorem configurationPhase_neg_mul (N : ℕ) (x : Configuration N) :
    G.neg.configurationPhase N x * G.configurationPhase N x = 1 := by
  rw [← G.neg.factor_configurationAngle, ← G.factor_configurationAngle, G.configurationAngle_neg]
  exact factor_neg_mul _ x

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem configurationPhase_memLp (u : ElectronicH1Space.L2 H (Fin N × Fin 3)) :
    MemLp (fun x => G.configurationPhase N x • u x) 2 volume :=
  (phase_memLp (G.configurationAngle_measurable N) u).ae_eq
    (ae_of_all _ fun x => by rw [G.factor_configurationAngle])

theorem gradient_source_memLp (u : ElectronicH1Complex.ComplexH1 H (Fin N × Fin 3))
    (q : Fin N × Fin 3) :
    MemLp (fun x => G.gradient q.2 (particle x q.1) • ElectronicH1Complex.value u x) 2 volume := by
  have h := particle_gradient_smul_memLp q.1 (ElectronicH1Complex.realEquiv u)
    (G.gradient_in_sum q.2)
  apply h.ae_eq
  exact ae_of_all _ fun x => by
    have he : (PhysicalSourceCoordinates.split q.1 x).1 = particle x q.1 := by ext a; rfl
    change G.gradient q.2 ((PhysicalSourceCoordinates.split q.1 x).1) •
      ElectronicH1Space.value (ElectronicH1Complex.realEquiv u) x =
        G.gradient q.2 (particle x q.1) • ElectronicH1Complex.value u x
    rw [ElectronicH1Complex.value_realEquiv, he]

theorem phase_gradient_source_memLp (u : ElectronicH1Complex.ComplexH1 H (Fin N × Fin 3))
    (q : Fin N × Fin 3) :
    MemLp (fun x => (G.configurationPhase N x *
      (Complex.I * (G.gradient q.2 (particle x q.1) : ℂ))) • ElectronicH1Complex.value u x)
      2 volume := by
  apply (G.gradient_source_memLp u q).mono
  · exact ((finite_localMemLp_two_locallyIntegrable
      ((G.weak_configurationPhase N).derivative_memLp q)).aestronglyMeasurable).smul
        (Lp.aestronglyMeasurable _)
  · exact ae_of_all _ fun x => by
      rw [norm_smul, norm_smul, norm_mul, norm_mul, G.norm_configurationPhase,
        Complex.norm_I, Complex.norm_real, one_mul, one_mul]

/-- Multiplication by exp(i sum S(x_j)) on the full electronic H1 graph. -/
def gaugeH1 (u : ElectronicH1Complex.ComplexH1 H (Fin N × Fin 3)) :
    ElectronicH1Complex.ComplexH1 H (Fin N × Fin 3) :=
  ElectronicH1Complex.realEquiv.symm
    (ElectronicH1Space.ofFunctions
      (fun x => G.configurationPhase N x • ElectronicH1Complex.value u x)
      (fun q x => G.configurationPhase N x • ElectronicH1Complex.derivative q u x +
        (G.configurationPhase N x * (Complex.I * (G.gradient q.2 (particle x q.1) : ℂ))) •
          ElectronicH1Complex.value u x)
      (G.configurationPhase_memLp (ElectronicH1Complex.value u))
      (fun q => (G.configurationPhase_memLp (ElectronicH1Complex.derivative q u)).add
        (G.phase_gradient_source_memLp u q))
      (weakH1Local_complex_smul_of_weighted
        (k := G.configurationPhase N)
        (dk := fun q x => G.configurationPhase N x *
          (Complex.I * (G.gradient q.2 (particle x q.1) : ℂ)))
        (f := fun x => ElectronicH1Complex.value u x)
        (df := fun q x => ElectronicH1Complex.derivative q u x)
        (G.weak_configurationPhase N) (ElectronicH1Complex.weak u)
        (fun K _ => (G.configurationPhase_memLp (ElectronicH1Complex.value u)).restrict K)
        (fun q K _ => (G.configurationPhase_memLp (ElectronicH1Complex.derivative q u)).restrict K)
        (fun q K _ => (G.phase_gradient_source_memLp u q).restrict K)))

theorem value_gaugeH1_ae (u : ElectronicH1Complex.ComplexH1 H (Fin N × Fin 3)) :
    ElectronicH1Complex.value (G.gaugeH1 u) =ᵐ[volume]
      fun x => G.configurationPhase N x • ElectronicH1Complex.value u x :=
  (G.configurationPhase_memLp (ElectronicH1Complex.value u)).coeFn_toLp

theorem value_gaugeH1 (u : ElectronicH1Complex.ComplexH1 H (Fin N × Fin 3)) :
    ElectronicH1Complex.value (G.gaugeH1 u) = phase (G.configurationAngle_measurable N)
      (ElectronicH1Complex.value u) := by
  apply Lp.ext
  filter_upwards [G.value_gaugeH1_ae u, phase_ae (G.configurationAngle_measurable N)
    (ElectronicH1Complex.value u)] with x hx hy
  rw [hx, hy, G.factor_configurationAngle]

theorem derivative_gaugeH1_ae (u : ElectronicH1Complex.ComplexH1 H (Fin N × Fin 3))
    (q : Fin N × Fin 3) :
    ElectronicH1Complex.derivative q (G.gaugeH1 u) =ᵐ[volume]
      fun x => G.configurationPhase N x • (ElectronicH1Complex.derivative q u x +
        Complex.I • (G.gradient q.2 (particle x q.1) • ElectronicH1Complex.value u x)) := by
  have h := ((G.configurationPhase_memLp (ElectronicH1Complex.derivative q u)).add
    (G.phase_gradient_source_memLp u q)).coeFn_toLp
  refine h.trans (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, smul_add, ← Complex.coe_smul, smul_smul, mul_assoc]

theorem neg_gaugeH1 (u : ElectronicH1Complex.ComplexH1 H (Fin N × Fin 3)) :
    G.neg.gaugeH1 (G.gaugeH1 u) = u := by
  apply ElectronicH1Complex.ext_ae
  filter_upwards [G.neg.value_gaugeH1_ae (G.gaugeH1 u), G.value_gaugeH1_ae u] with x hx hy
  rw [hx, hy, smul_smul, G.configurationPhase_neg_mul, one_smul]

attribute [irreducible] gaugeH1

end GptLean.TransformationsGauge.WeakSpatialGauge
