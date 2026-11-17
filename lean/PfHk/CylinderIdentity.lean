import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The Hilbert-valued integration identity behind `pf-cylinder-commutator`.
The symmetric and skew expressions and their boundary flux are defined
explicitly. The identity is derived from differentiation and integration,
not supplied as a numerical hypothesis.

The angular and radiation operators may be unbounded. Only their values
on the chosen curve and the quadratic-form product rules enter. The
physical realization of these product rules is a separate application.
-/

noncomputable section

namespace PfHk.CylinderIdentity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

open MeasureTheory Filter Set
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def symmetricPart (τ c : ℝ) (p r : ℝ → ℝ)
    (z ddz k q : ℝ → H) (t : ℝ) : H :=
  -ddz t + k t + c ^ 2 • z t + r t • q t - (τ ^ 2 * p t ^ 2) • z t

def skewPart (τ : ℝ) (p b : ℝ → ℝ) (z dz : ℝ → H) (t : ℝ) : H :=
  (2 * τ * p t) • dz t + (τ * b t) • z t

def commutatorDensity (τ : ℝ) (p b ddb r kv qv : ℝ → ℝ)
    (z dz q : ℝ → H) (t : ℝ) : ℝ :=
  4 * τ * b t * inner ℝ (dz t) (dz t) +
  4 * τ ^ 3 * p t ^ 2 * b t * inner ℝ (z t) (z t) -
  τ * ddb t * inner ℝ (z t) (z t) - 2 * τ * p t * kv t +
  4 * τ * p t * r t * inner ℝ (z t) (q t) - 2 * τ * p t * r t * qv t

def boundaryFlux (τ c : ℝ) (p b db r : ℝ → ℝ)
    (z dz k q : ℝ → H) (t : ℝ) : ℝ :=
  -2 * τ * p t * inner ℝ (dz t) (dz t) -
  2 * τ * b t * inner ℝ (dz t) (z t) +
  τ * db t * inner ℝ (z t) (z t) +
  2 * τ * p t * inner ℝ (z t) (k t) +
  2 * τ * c ^ 2 * p t * inner ℝ (z t) (z t) +
  2 * τ * p t * r t * inner ℝ (z t) (q t) -
  2 * τ ^ 3 * p t ^ 3 * inner ℝ (z t) (z t)

/-- The exact derivative of the boundary flux. The two quadratic-form
product rules are the usual differentiation rules for a moving symmetric
operator, restricted to this curve. -/
theorem boundaryFlux_hasDerivAt (τ c : ℝ)
    {p b db ddb r kv qv : ℝ → ℝ} {z dz ddz k q : ℝ → H} {t : ℝ}
    (hp : HasDerivAt p (b t) t) (hb : HasDerivAt b (db t) t)
    (hdb : HasDerivAt db (ddb t) t) (hr : HasDerivAt r (-2 * r t) t)
    (hz : HasDerivAt z (dz t) t) (hdz : HasDerivAt dz (ddz t) t)
    (hk : HasDerivAt (fun s => inner ℝ (z s) (k s))
      (2 * inner ℝ (dz t) (k t) + kv t) t)
    (hq : HasDerivAt (fun s => inner ℝ (z s) (q s))
      (2 * inner ℝ (dz t) (q t) + qv t) t) :
    HasDerivAt (boundaryFlux τ c p b db r z dz k q)
      (2 * inner ℝ (symmetricPart τ c p r z ddz k q t)
          (skewPart τ p b z dz t) -
        commutatorDensity τ p b ddb r kv qv z dz q t) t := by
  have hzz := hz.inner ℝ hz
  have hdz2 := hdz.inner ℝ hdz
  have hdzz := hdz.inner ℝ hz
  have h₁ := (hp.const_mul (-2 * τ)).mul hdz2
  have h₂ := (hb.const_mul (2 * τ)).mul hdzz
  have h₃ := (hdb.const_mul τ).mul hzz
  have h₄ := (hp.const_mul (2 * τ)).mul hk
  have h₅ := (hp.const_mul (2 * τ * c ^ 2)).mul hzz
  have h₆ := ((hp.const_mul (2 * τ)).mul hr).mul hq
  have h₇ := ((hp.pow 3).const_mul (2 * τ ^ 3)).mul hzz
  convert (((((h₁.sub h₂).add h₃).add h₄).add h₅).add h₆).sub h₇ using 1 <;> try rfl
  · simp only [symmetricPart, skewPart, commutatorDensity,
      inner_add_left, inner_add_right, inner_sub_left,
      inner_neg_left, real_inner_smul_left, real_inner_smul_right,
      Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub]
    simp only [real_inner_comm]
    ring

/-- The commutator identity as an equality of actual integrals. Integrable
boundary flux is enough to remove the boundary term. For compactly supported
smooth cylinder vectors it follows directly from compact support. -/
theorem integrated_commutator (τ c : ℝ)
    {p b db ddb r kv qv : ℝ → ℝ} {z dz ddz k q : ℝ → H}
    (hp : ∀ t, HasDerivAt p (b t) t) (hb : ∀ t, HasDerivAt b (db t) t)
    (hdb : ∀ t, HasDerivAt db (ddb t) t) (hr : ∀ t, HasDerivAt r (-2 * r t) t)
    (hz : ∀ t, HasDerivAt z (dz t) t) (hdz : ∀ t, HasDerivAt dz (ddz t) t)
    (hk : ∀ t, HasDerivAt (fun s => inner ℝ (z s) (k s))
      (2 * inner ℝ (dz t) (k t) + kv t) t)
    (hq : ∀ t, HasDerivAt (fun s => inner ℝ (z s) (q s))
      (2 * inner ℝ (dz t) (q t) + qv t) t)
    (hflux : Integrable (boundaryFlux τ c p b db r z dz k q))
    (hcross : Integrable (fun t => 2 * inner ℝ
      (symmetricPart τ c p r z ddz k q t) (skewPart τ p b z dz t)))
    (hmain : Integrable (commutatorDensity τ p b ddb r kv qv z dz q)) :
    (∫ t, 2 * inner ℝ (symmetricPart τ c p r z ddz k q t)
      (skewPart τ p b z dz t)) =
      ∫ t, commutatorDensity τ p b ddb r kv qv z dz q t := by
  have h := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun t => boundaryFlux_hasDerivAt τ c (hp t) (hb t) (hdb t) (hr t)
      (hz t) (hdz t) (hk t) (hq t)) (hcross.sub hmain) hflux
  rw [integral_sub hcross hmain] at h
  exact sub_eq_zero.mp h

/-- Half-cylinder version, with the actual lower-end boundary and the
limit at infinity specified. The logarithmic weights are smooth here
when the lower endpoint is positive. -/
theorem integrated_commutator_Ioi (τ c t₀ : ℝ)
    {p b db ddb r kv qv : ℝ → ℝ} {z dz ddz k q : ℝ → H}
    (hp : ∀ t ∈ Ici t₀, HasDerivAt p (b t) t)
    (hb : ∀ t ∈ Ici t₀, HasDerivAt b (db t) t)
    (hdb : ∀ t ∈ Ici t₀, HasDerivAt db (ddb t) t)
    (hr : ∀ t ∈ Ici t₀, HasDerivAt r (-2 * r t) t)
    (hz : ∀ t ∈ Ici t₀, HasDerivAt z (dz t) t)
    (hdz : ∀ t ∈ Ici t₀, HasDerivAt dz (ddz t) t)
    (hk : ∀ t ∈ Ici t₀, HasDerivAt (fun s => inner ℝ (z s) (k s))
      (2 * inner ℝ (dz t) (k t) + kv t) t)
    (hq : ∀ t ∈ Ici t₀, HasDerivAt (fun s => inner ℝ (z s) (q s))
      (2 * inner ℝ (dz t) (q t) + qv t) t)
    (hzero : boundaryFlux τ c p b db r z dz k q t₀ = 0)
    (hinfty : Tendsto (boundaryFlux τ c p b db r z dz k q) atTop (𝓝 0))
    (hcross : IntegrableOn (fun t => 2 * inner ℝ
      (symmetricPart τ c p r z ddz k q t) (skewPart τ p b z dz t)) (Ioi t₀))
    (hmain : IntegrableOn (commutatorDensity τ p b ddb r kv qv z dz q) (Ioi t₀)) :
    (∫ t in Ioi t₀, 2 * inner ℝ (symmetricPart τ c p r z ddz k q t)
      (skewPart τ p b z dz t)) =
      ∫ t in Ioi t₀, commutatorDensity τ p b ddb r kv qv z dz q t := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => boundaryFlux_hasDerivAt τ c (hp t ht) (hb t ht) (hdb t ht)
      (hr t ht) (hz t ht) (hdz t ht) (hk t ht) (hq t ht))
    (hcross.sub hmain) hinfty
  rw [hzero, sub_self, integral_sub hcross hmain] at h
  exact sub_eq_zero.mp h

def multiplierFlux (b db : ℝ → ℝ) (z dz : ℝ → H) (t : ℝ) : ℝ :=
  b t * inner ℝ (dz t) (z t) - (db t / 2) * inner ℝ (z t) (z t)

def multiplierDensity (τ c : ℝ) (p b ddb r : ℝ → ℝ)
    (z dz k q : ℝ → H) (t : ℝ) : ℝ :=
  b t * (inner ℝ (dz t) (dz t) + inner ℝ (z t) (k t) +
    r t * inner ℝ (z t) (q t) + c ^ 2 * inner ℝ (z t) (z t)) -
    τ ^ 2 * p t ^ 2 * b t * inner ℝ (z t) (z t) -
    (ddb t / 2) * inner ℝ (z t) (z t)

/-- Differentiation gives the angular multiplier identity and its precise
second-derivative correction. No multiplier estimate is assumed. -/
theorem multiplierFlux_hasDerivAt (τ c : ℝ)
    {p b db ddb r : ℝ → ℝ} {z dz ddz k q : ℝ → H} {t : ℝ}
    (hb : HasDerivAt b (db t) t) (hdb : HasDerivAt db (ddb t) t)
    (hz : HasDerivAt z (dz t) t) (hdz : HasDerivAt dz (ddz t) t) :
    HasDerivAt (multiplierFlux b db z dz)
      (multiplierDensity τ c p b ddb r z dz k q t -
        inner ℝ (symmetricPart τ c p r z ddz k q t) (b t • z t)) t := by
  have h₁ := hb.mul (hdz.inner ℝ hz)
  have h₂ := (hdb.div_const 2).mul (hz.inner ℝ hz)
  convert h₁.sub h₂ using 1 <;> try rfl
  · simp only [multiplierDensity, symmetricPart, inner_add_left,
      inner_sub_left, inner_neg_left, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_comm]
    ring

theorem integrated_multiplier_Ioi (τ c t₀ : ℝ)
    {p b db ddb r : ℝ → ℝ} {z dz ddz k q : ℝ → H}
    (hb : ∀ t ∈ Ici t₀, HasDerivAt b (db t) t)
    (hdb : ∀ t ∈ Ici t₀, HasDerivAt db (ddb t) t)
    (hz : ∀ t ∈ Ici t₀, HasDerivAt z (dz t) t)
    (hdz : ∀ t ∈ Ici t₀, HasDerivAt dz (ddz t) t)
    (hzero : multiplierFlux b db z dz t₀ = 0)
    (hinfty : Tendsto (multiplierFlux b db z dz) atTop (𝓝 0))
    (hmain : IntegrableOn (multiplierDensity τ c p b ddb r z dz k q) (Ioi t₀))
    (hpair : IntegrableOn (fun t =>
      inner ℝ (symmetricPart τ c p r z ddz k q t) (b t • z t)) (Ioi t₀)) :
    (∫ t in Ioi t₀, inner ℝ (symmetricPart τ c p r z ddz k q t) (b t • z t)) =
      ∫ t in Ioi t₀, multiplierDensity τ c p b ddb r z dz k q t := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => multiplierFlux_hasDerivAt τ c (hb t ht) (hdb t ht) (hz t ht) (hdz t ht))
    (hmain.sub hpair) hinfty
  rw [hzero, sub_self, integral_sub hmain hpair] at h
  exact (sub_eq_zero.mp h).symm

/-- The norm-square form of the commutator identity. -/
theorem integral_norm_square_identity {S B : ℝ → H} {D : ℝ → ℝ}
    (hS : Integrable (fun t => ‖S t‖ ^ 2))
    (hB : Integrable (fun t => ‖B t‖ ^ 2))
    (hcross : Integrable (fun t => 2 * inner ℝ (S t) (B t)))
    (hcommutator : (∫ t, 2 * inner ℝ (S t) (B t)) = ∫ t, D t) :
    (∫ t, ‖S t + B t‖ ^ 2) = (∫ t, ‖S t‖ ^ 2) +
      (∫ t, ‖B t‖ ^ 2) + ∫ t, D t := by
  calc
    _ = ∫ t, (‖S t‖ ^ 2 + ‖B t‖ ^ 2) + 2 * inner ℝ (S t) (B t) := by
      apply integral_congr_ae
      filter_upwards with t
      nlinarith [norm_add_sq_real (S t) (B t)]
    _ = _ := by
      have hsum := integral_add (hS.add hB) hcross
      have hsum₂ := integral_add hS hB
      simp only [Pi.add_apply] at hsum hsum₂
      rw [hsum, hsum₂, hcommutator]

end PfHk.CylinderIdentity
