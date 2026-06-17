import Mathlib.MeasureTheory.Integral.IntegrableOn

example (δ : ℝ) : (δ / 2)⁻¹ = 2 / δ := by
  by_cases hδ : δ = 0
  · subst hδ
    norm_num
  · field_simp [hδ]
