import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Order.Interval.Set.UnorderedInterval

example : ((-(1 / 2 : ℝ) : ℂ)) = -((1 : ℂ) / (2 : ℂ)) := by
  exact Complex.ofReal_div (-(1 : ℝ)) 2

example : (((1 / 2 : ℝ) : ℂ)) = (1 : ℂ) / (2 : ℂ) := by
  exact Complex.ofReal_div 1 2
