import PfHk.SymmetricGraphExtension

/-! The ordinary Kato--Rellich theorem as a universal operator-theory input.
Its two graphs are abstract Hilbert-space relations. The second graph is an
algebraic perturbation on the first graph's domain, not a weak form graph.
The physical weak realization is identified separately by the proved
symmetric-extension theorem. -/

noncomputable section
namespace PfHk.KatoRellichBackground

open SymmetricGraphExtension

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def ShiftSurjective (G : H → H → Prop) (z : ℂ) : Prop :=
  ∀ f : H, ∃ u v, G u v ∧ v + z • u = f

/-- The standard resolvent characterization of self-adjointness. -/
structure SelfAdjointGraph (G : H → H → Prop) : Prop where
  symmetric : SymmetricGraphExtension.Symmetric G
  dense : Dense {u | ∃ v, G u v}
  positiveShift : ShiftSurjective G Complex.I
  negativeShift : ShiftSurjective G (-Complex.I)

theorem SelfAdjointGraph.single_valued {G : H → H → Prop} (hG : SelfAdjointGraph G)
    {u v w : H} (hv : G u v) (hw : G u w) : v = w := by
  apply hG.dense.eq_of_inner_right ℂ
  rintro x ⟨y, hy⟩
  exact (hG.symmetric x y u v hy hv).trans (hG.symmetric x y u w hy hw).symm

/-- Kato--Rellich, stated without physical quantities or form-domain
conclusions. Relative bounds have the usual strict coefficient less than one. -/
structure StandardKatoRellich where
  resolve : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (G P : H → H → Prop),
    SelfAdjointGraph G → SymmetricGraphExtension.Symmetric P →
    (∀ u, (∃ v, G u v) ↔ ∃ v, P u v) →
    ∀ a b : ℝ, 0 ≤ a → a < 1 → 0 ≤ b →
    (∀ u v w, G u v → P u w → ‖w - v‖ ≤ a * ‖v‖ + b * ‖u‖) →
    ShiftSurjective P Complex.I

/-- After Kato--Rellich, a symmetric weak realization that contains the
algebraic sum equals that sum. The containment is proved from the actual
form expansion in physical applications. -/
theorem weak_graph_eq [CompleteSpace H] (B : StandardKatoRellich)
    (G P E : H → H → Prop) (hG : SelfAdjointGraph G)
    (hE : SymmetricGraphExtension.Symmetric E) (hPE : ∀ u v, P u v → E u v)
    (hdom : ∀ u, (∃ v, G u v) ↔ ∃ v, P u v)
    (a b : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hrel : ∀ u v w, G u v → P u w → ‖w - v‖ ≤ a * ‖v‖ + b * ‖u‖) :
    ∀ u v, E u v ↔ P u v := by
  have hP : SymmetricGraphExtension.Symmetric P := fun u v u' v' hu hv =>
    hE u v u' v' (hPE u v hu) (hPE u' v' hv)
  exact eq_of_resolvent_surjective P E hE hPE
    (B.resolve H G P hG hP hdom a b ha ha1 hb hrel)

end PfHk.KatoRellichBackground
