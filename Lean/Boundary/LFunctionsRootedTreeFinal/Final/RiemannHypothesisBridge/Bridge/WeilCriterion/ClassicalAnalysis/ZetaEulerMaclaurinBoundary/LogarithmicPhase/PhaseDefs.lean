import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.ComplexSupport

/-!
# Phase definitions for logarithmic phase estimates

This file owns the basic logarithmic phase functions and their definitional
expansions before derivative estimates are introduced.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Logarithmic-phase partial sums for the boundary-line oscillator `n^{-it}`. -/
def Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
    (t : ℝ)
    (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((n : ℂ) ^ (-(t : ℂ) * Complex.I))

/-- Definitional expansion of the logarithmic-phase partial sum. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq
    (t : ℝ)
    (N : ℕ) :
    Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t N =
      ∑ n ∈ Finset.Icc 1 N,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  rfl

/-- The continuous logarithmic phase whose positive integer samples are
`n^{-it}`. -/
def Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction
    (t : ℝ)
    (x : ℝ) : ℂ :=
  Complex.exp ((-(t : ℂ) * Complex.I) * (Real.log x : ℂ))

/-- The real scalar phase behind the boundary-line oscillator. -/
def Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
    (t : ℝ)
    (x : ℝ) : ℝ :=
  -t * Real.log x

/-- The complex logarithmic phase is the exponential of the real scalar phase. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_realPhase
    (t : ℝ)
    (x : ℝ) :
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x : ℂ)) := by
  have hphase :
      (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x : ℂ)) =
        (-(t : ℂ) * Complex.I) * (Real.log x : ℂ) := by
    calc
      Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x : ℂ) =
          Complex.I * ((-t * Real.log x : ℝ) : ℂ) := by
        rfl
      _ = Complex.I * ((-t : ℝ) : ℂ) * (Real.log x : ℂ) := by
        calc
          Complex.I * ((-t * Real.log x : ℝ) : ℂ) =
              Complex.I * (((-t : ℝ) : ℂ) * (Real.log x : ℂ)) := by
            exact congrArg (fun z : ℂ => Complex.I * z)
              (Complex.ofReal_mul (-t) (Real.log x))
          _ = Complex.I * ((-t : ℝ) : ℂ) * (Real.log x : ℂ) := by
            exact (mul_assoc Complex.I ((-t : ℝ) : ℂ) (Real.log x : ℂ)).symm
      _ = ((-t : ℝ) : ℂ) * Complex.I * (Real.log x : ℂ) := by
        exact congrArg (fun z : ℂ => z * (Real.log x : ℂ))
          (mul_comm Complex.I ((-t : ℝ) : ℂ))
      _ = (-(t : ℂ) * Complex.I) * (Real.log x : ℂ) := by
        exact congrArg (fun z : ℂ => (z * Complex.I) * (Real.log x : ℂ))
          (Complex.ofReal_neg t)
  exact congrArg Complex.exp hphase.symm

/-- Positive real samples of the logarithmic phase agree with the complex-power
notation used in the Dirichlet-polynomial partial sums. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
      (x : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  let a : ℂ := -(t : ℂ) * Complex.I
  have hx_complex_ne : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  have hlog : (Real.log x : ℂ) = Complex.log (x : ℂ) :=
    Complex.ofReal_log hx.le
  have hcomm :
      a * (Real.log x : ℂ) = (Real.log x : ℂ) * a :=
    mul_comm a (Real.log x : ℂ)
  have hreplace :
      (Real.log x : ℂ) * a = Complex.log (x : ℂ) * a :=
    congrArg (fun z : ℂ => z * a) hlog
  calc
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
        Complex.exp (a * (Real.log x : ℂ)) := by
      rfl
    _ = Complex.exp ((Real.log x : ℂ) * a) :=
      congrArg Complex.exp hcomm
    _ = Complex.exp (Complex.log (x : ℂ) * a) :=
      congrArg Complex.exp hreplace
    _ = (x : ℂ) ^ a :=
      (Complex.cpow_def_of_ne_zero hx_complex_ne a).symm

/-- Integer samples of the continuous logarithmic phase are the terms
`n^{-it}`. -/
theorem Complex.logarithmicPhase_integer_sample_eq
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n =
      (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  have hn_real : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr hn
  exact
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
      t hn_real

end

end LFunctions
end Boundary
