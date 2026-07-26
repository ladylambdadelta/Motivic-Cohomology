import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlana
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaCore

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Gamma avoids the principal-log slit on the open right half-plane. -/
def Complex.GammaRightHalfPlaneSlitPlaneControl : Prop :=
  ∀ z : ℂ, 0 < z.re → Complex.Gamma z ∈ Complex.slitPlane

/- Principal-log control is local at an already admissible Gamma value. -/
def Complex.GammaLocalSlitPlaneControl : Prop :=
  ∀ z : ℂ, Complex.Gamma z ∈ Complex.slitPlane →
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z ε →
        Complex.Gamma w ∈ Complex.slitPlane

/-- The finite Abel-Plana decomposition for the Binet logarithmic Gamma
approximation on the open right half-plane. -/
def Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition : Prop :=
  ∀ z : ℂ,
    0 < z.re →
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
          Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            Complex.binetAbelPlanaFiniteContourRemainder N z

/-- Exact branch-coherence hypotheses required by the Binet owner theorem for
the principal logarithm of `Gamma`. -/
def Complex.gammaBinetPrincipalLogCoherence : Prop :=
  (∀ z : ℂ, 0 < z.re → Complex.Gamma z ∈ Complex.slitPlane) ∧
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

/-- The Abel-Plana Binet logarithm branch exponentiates to Gamma on the open
right half-plane. -/
def Complex.BinetLogGammaBranchExponentialControl : Prop :=
  ∀ z : ℂ,
    0 < z.re →
      Complex.exp (Complex.binetLogGammaBranch z) =
        Complex.Gamma z

/-- Branch-correct coherence package for Binet's logarithmic Gamma formula. -/
def Complex.binetBranchLogGammaCoherence : Prop :=
  Complex.BinetLogGammaBranchExponentialControl ∧
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

/- The carrier-restricted principal branch package used by scheduled
consumers. -/
def Complex.BinetCarrierBranchCoherence : Prop :=
  Complex.BinetLogGammaBranchExponentialControl ∧
  Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition ∧
  Complex.GammaLocalSlitPlaneControl

/- The contour carrier needs local slit-plane neighborhoods, not the stronger
global assertion that the whole right-half-plane Gamma image avoids the
principal cut. -/
def Complex.BinetRightHalfPlaneCarrierControl : Prop :=
  Complex.BinetLogGammaBranchExponentialControl ∧
  (∀ z : ℂ, 0 < z.re → Complex.Gamma z ≠ 0) ∧
  Complex.GammaLocalSlitPlaneControl ∧
  Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition

end

end LFunctions
end Boundary
