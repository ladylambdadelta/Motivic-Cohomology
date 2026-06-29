import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaOwner
import Mathlib

import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteFormula
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetTailContour
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FiniteOrderAlgebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.RightCriticalStripCompact.Owner

/-!
# Binet kernel and sectorial Gamma seed estimates

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

def Complex.BinetSecondFormulaBranchCoherence : Prop :=
  (∀ z : ℂ, 0 < z.re →
      Complex.exp (Complex.binetLogGammaBranch z) = Complex.Gamma z) ∧
  (∀ x : ℝ,
    0 < x →
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
          Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
              Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) ∧
  (∀ z : ℂ,
    0 < z.re →
      (∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
              Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
      (∀ᶠ y : ℂ in 𝓝 z,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
            Complex.binetAbelPlanaFiniteMainTerm N y +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                Complex.binetAbelPlanaFiniteContourRemainder N y))

/-- The owner-level full-sector branch-tail absorption input. -/
theorem Complex.BinetSecondFormulaBranchCoherence.of_owner_components
    (hgamma :
      ∀ z : ℂ, 0 < z.re →
        Complex.exp (Complex.binetLogGammaBranch z) = Complex.Gamma z)
    (hreal :
      ∀ x : ℝ,
        0 < x →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
              Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                  Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ))
    (hopen :
      ∀ z : ℂ,
        0 < z.re →
          (∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
          (∀ᶠ y : ℂ in 𝓝 z,
            ∀ N : ℕ,
              Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                Complex.binetAbelPlanaFiniteMainTerm N y +
                  Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                    Complex.binetAbelPlanaFiniteContourRemainder N y)) :
    Complex.BinetSecondFormulaBranchCoherence :=
  ⟨hgamma, hreal, hopen⟩

end
end LFunctions
end Boundary
