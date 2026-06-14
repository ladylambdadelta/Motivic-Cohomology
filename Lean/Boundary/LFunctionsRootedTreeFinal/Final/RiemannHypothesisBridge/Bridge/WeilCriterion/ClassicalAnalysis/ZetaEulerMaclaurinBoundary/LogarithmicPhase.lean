import LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.BoundaryLine

/-!
# Logarithmic phase estimates

This file owns the oscillatory phase `n^{-it}` input used by the
Euler-Maclaurin boundary argument.  The phase is logarithmic, not a
constant-ratio geometric progression.
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

/-- The standard first-derivative-test owner root for the concrete logarithmic
phase.  This is the analytic input behind the Euler-Maclaurin boundary
package; cf. Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A *
                  (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                    Real.log (2 + N) := by
  sorry

/-- First-derivative estimate for the logarithmic phase sums on the boundary
line.

The previous scaffold stated an `O(log N)` bound for the unweighted sums
`∑ n^{-it}`.  The owner-level first-derivative estimate has the standard
oscillatory-sum size shown here; the reciprocal Abel weight is introduced in
`AbelTail`. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A *
                  (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                    Real.log (2 + N) := by
  exact Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound

end

end LFunctions
end Boundary
