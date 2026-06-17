import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Order.Interval.Set.UnorderedInterval

example : ((-(1 / 2 : ℝ) : ℂ)) = (-(1 / 2 : ℂ)) := by
  have hreal : (-(1 / 2 : ℝ)) = (-(1 : ℝ)) / 2 := by
    nlinarith
  calc
    ((-(1 / 2 : ℝ) : ℂ)) = (((-(1 : ℝ)) / 2 : ℝ) : ℂ) := by
      exact congrArg Complex.ofReal hreal
    _ = ((-(1 : ℝ) : ℂ) / (2 : ℂ)) := by
      exact Complex.ofReal_div (-(1 : ℝ)) 2
    _ = (-(1 / 2 : ℂ)) := by
      rfl

example : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by
  have hreal : (1 / 2 : ℝ) = (1 : ℝ) / 2 := by
    rfl
  calc
    (((1 / 2 : ℝ) : ℂ)) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by
      exact congrArg Complex.ofReal hreal
    _ = ((1 : ℂ) / (2 : ℂ)) := by
      exact Complex.ofReal_div 1 2
    _ = (1 / 2 : ℂ) := by
      rfl
