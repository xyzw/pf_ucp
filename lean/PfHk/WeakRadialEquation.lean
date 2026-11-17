import PfHk.WeakCylinderForm
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Module

/-! Ordinary radial integration by parts and the smooth-test fundamental
lemma, with values in an arbitrary real Banach space. -/

noncomputable section
namespace PfHk.WeakRadialEquation

open MeasureTheory Set
open scoped Topology InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 100000

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem density_algebra (a d c r : ℝ) (z dz ddz A T source : F) :
    (d + c * a) • (dz + c • z) + a • A + (r * a) • T =
      (d • (dz + c • z) + a • (ddz + c • dz)) +
        a • (A + r • T - source - ddz + c ^ 2 • z) + a • source := by
  module

private theorem compact_smul_integrable {a : ℝ → ℝ} {f : ℝ → F}
    (ha : Continuous a) (hs : HasCompactSupport a) (hf : Continuous f) :
    Integrable (fun t => a t • f t) :=
  (ha.smul hf).integrable_of_hasCompactSupport hs.smul_right

/-- A weak radial equation determines the remaining continuous angular
pairing at every interior time. -/
theorem angular_eq_of_tests (c l r : ℝ)
    (z dz ddz A T source : ℝ → F) (q : ℝ → ℝ)
    (hz : ∀ t, HasDerivAt z (dz t) t) (hdz : ∀ t, HasDerivAt dz (ddz t) t)
    (hddz : Continuous ddz) (hA : Continuous A) (hT : Continuous T)
    (hsource : Continuous source) (hq : Continuous q)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo l r →
      (∫ t in Icc l r, (deriv η t + c * η t) • (dz t + c • z t) +
        η t • A t + (q t * η t) • T t) = ∫ t in Icc l r, η t • source t)
    {t : ℝ} (ht : t ∈ Ioo l r) :
    A t = source t + ddz t - c ^ 2 • z t - q t • T t := by
  have hzc : Continuous z := continuous_iff_continuousAt.mpr fun t => (hz t).continuousAt
  have hdzc : Continuous dz := continuous_iff_continuousAt.mpr fun t => (hdz t).continuousAt
  let f : ℝ → F := fun s => A s + q s • T s - source s - ddz s + c ^ 2 • z s
  have hfc : Continuous f :=
    (((hA.add (hq.smul hT)).sub hsource).sub hddz).add (hzc.const_smul (c ^ 2))
  have htests (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
      (hs : HasCompactSupport η) (hsub : tsupport η ⊆ Ioo l r) :
      (∫ s, η s • f s) = 0 := by
    have hηd : Continuous (deriv η) := hη.continuous_deriv (by simp)
    have hp : Continuous (fun s => dz s + c • z s) := hdzc.add (hzc.const_smul c)
    have hdp : Continuous (fun s => ddz s + c • dz s) := hddz.add (hdzc.const_smul c)
    let flux : ℝ → F := fun s => η s • (dz s + c • z s)
    let fluxDerivative : ℝ → F := fun s =>
      deriv η s • (dz s + c • z s) + η s • (ddz s + c • dz s)
    have hderivative : ∀ s, HasDerivAt flux (fluxDerivative s) s := by
      intro s
      have h := ((hη.differentiable (by simp) s).hasDerivAt).smul
        ((hdz s).add ((hz s).const_smul c))
      change HasDerivAt flux
        (η s • (ddz s + c • dz s) + deriv η s • (dz s + c • z s)) s at h
      have he : fluxDerivative s =
          η s • (ddz s + c • dz s) + deriv η s • (dz s + c • z s) := add_comm _ _
      rw [← he] at h
      exact h
    have hflux : Integrable flux := compact_smul_integrable hη.continuous hs hp
    have hdflux : Integrable fluxDerivative :=
      (compact_smul_integrable hηd hs.deriv hp).add
        (compact_smul_integrable hη.continuous hs hdp)
    have hzero : (∫ s, fluxDerivative s) = 0 :=
      integral_eq_zero_of_hasDerivAt_of_integrable hderivative hdflux hflux
    have hf : Integrable (fun s => η s • f s) := compact_smul_integrable hη.continuous hs hfc
    have hsrc : Integrable (fun s => η s • source s) :=
      compact_smul_integrable hη.continuous hs hsource
    have houtside (s : ℝ) (hsI : s ∉ Icc l r) : η s = 0 ∧ deriv η s = 0 := by
      have hts : s ∉ tsupport η := fun h => hsI (Ioo_subset_Icc_self (hsub h))
      exact ⟨image_eq_zero_of_notMem_tsupport hts,
        image_eq_zero_of_notMem_tsupport (fun h => hts (tsupport_deriv_subset h))⟩
    have hleft := setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := (volume : Measure ℝ)) (s := Icc l r)
      (f := fun s => (deriv η s + c * η s) • (dz s + c • z s) +
        η s • A s + (q s * η s) • T s) (fun s hsI => by
          rcases houtside s hsI with ⟨h₁, h₂⟩
          simp only [h₁, h₂, mul_zero, add_zero, zero_smul, zero_add])
    have hright := setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := (volume : Measure ℝ)) (s := Icc l r) (f := fun s => η s • source s)
      (fun s hsI => by rw [(houtside s hsI).1, zero_smul])
    have hglobal := hleft.symm.trans ((hweak η hη hs hsub).trans hright)
    have hid : (∫ s, (deriv η s + c * η s) • (dz s + c • z s) +
        η s • A s + (q s * η s) • T s) =
        (∫ s, fluxDerivative s) + (∫ s, η s • f s) + ∫ s, η s • source s := by
      have he : (fun s => (deriv η s + c * η s) • (dz s + c • z s) +
          η s • A s + (q s * η s) • T s) =
          fun s => fluxDerivative s + η s • f s + η s • source s :=
        funext fun s => density_algebra _ _ _ _ _ _ _ _ _ _
      have hsum := integral_add (hdflux.add hf) hsrc
      have hpair := integral_add hdflux hf
      dsimp only [Pi.add_apply] at hsum hpair
      rw [he, hsum, hpair]
    have hcancel := hid.symm.trans hglobal
    rw [hzero, zero_add] at hcancel
    exact add_right_cancel (hcancel.trans (zero_add _).symm)
  have hae : ∀ᵐ s ∂volume, s ∈ Ioo l r → f s = 0 :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hfc.locallyIntegrable.locallyIntegrableOn (Ioo l r)) htests
  have hrestrict : f =ᵐ[(volume : Measure ℝ).restrict (Ioo l r)] 0 := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioo] with s hs hmem
    exact hs hmem
  have hzero := Measure.eqOn_open_of_ae_eq hrestrict isOpen_Ioo hfc.continuousOn
    continuous_const.continuousOn ht
  change A t + q t • T t - source t - ddz t + c ^ 2 • z t = 0 at hzero
  calc
    A t = (A t + q t • T t - source t - ddz t + c ^ 2 • z t) +
        (source t + ddz t - c ^ 2 • z t - q t • T t) := by abel
    _ = _ := by rw [hzero, zero_add]

/-- Scalar pairing version for the weak angular equation of a Hilbert
valued curve. All differentiation is performed before specialization. -/
theorem angular_pairing_eq_of_tests {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (v : H) (c l r : ℝ) (z dz ddz source : ℝ → H) (A T q : ℝ → ℝ)
    (hz : ∀ t, HasDerivAt z (dz t) t) (hdz : ∀ t, HasDerivAt dz (ddz t) t)
    (hddz : Continuous ddz) (hA : Continuous A) (hT : Continuous T)
    (hsource : Continuous source) (hq : Continuous q)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo l r →
      (∫ t in Icc l r, (deriv η t + c * η t) * ⟪v, dz t + c • z t⟫_ℝ +
        η t * A t + (q t * η t) * T t) = ∫ t in Icc l r, η t * ⟪v, source t⟫_ℝ)
    {t : ℝ} (ht : t ∈ Ioo l r) :
    A t = ⟪v, source t + ddz t - c ^ 2 • z t⟫_ℝ - q t * T t := by
  let L : H →L[ℝ] ℝ := innerSL ℝ v
  have hz' (s : ℝ) : HasDerivAt (fun t => L (z t)) (L (dz s)) s :=
    L.hasFDerivAt.comp_hasDerivAt s (hz s)
  have hdz' (s : ℝ) : HasDerivAt (fun t => L (dz t)) (L (ddz s)) s :=
    L.hasFDerivAt.comp_hasDerivAt s (hdz s)
  have h := angular_eq_of_tests c l r (fun t => L (z t)) (fun t => L (dz t))
    (fun t => L (ddz t)) A T (fun t => L (source t)) q hz' hdz'
    (L.continuous.comp hddz) hA hT (L.continuous.comp hsource) hq
    (fun η hη hs hsub => by
      simpa only [L, smul_eq_mul, innerSL_apply_apply, inner_add_right, inner_smul_right]
        using hweak η hη hs hsub) ht
  simpa only [L, smul_eq_mul, innerSL_apply_apply, inner_add_right, inner_sub_right,
    inner_smul_right] using h

end PfHk.WeakRadialEquation
