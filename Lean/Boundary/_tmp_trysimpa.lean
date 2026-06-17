import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Order.Interval.Set.UnorderedInterval

example : ((-(1 / 2 : ℝ) : ℂ)) = (-(1 / 2 : ℂ)) := by
  simpa [Complex.ofReal_div] using (Complex.ofReal_div (-(1 : ℝ)) 2)

