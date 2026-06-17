import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Order.Interval.Set.UnorderedInterval

example : (-(1 / 2 : ℝ)) = (-(1 : ℝ)) / 2 := by
  rw [← neg_div]
