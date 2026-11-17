import PfHk.InfiniteOrder

namespace PfHk.InfiniteOrder

theorem FlatAtZero.mono {U W : ℝ → ℝ} (hU : FlatAtZero U)
    (hWU : ∀ r, 0 < r → W r ≤ U r) : FlatAtZero W := by
  intro m
  obtain ⟨c, hc, R, hR, hb⟩ := hU m
  exact ⟨c, hc, R, hR, fun r hr hrR => (hWU r hr).trans (hb r hr hrR)⟩

end PfHk.InfiniteOrder
