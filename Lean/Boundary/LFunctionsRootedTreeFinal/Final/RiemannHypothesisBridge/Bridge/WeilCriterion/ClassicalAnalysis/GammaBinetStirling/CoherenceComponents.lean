import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SectorialLogNorm

/-!
# Binet principal-log coherence components

This file owns small assembly lemmas for the coherence package used by the
principal-log version of Binet's formula.  It does not assert the missing
Gamma branch-cut theorem; it isolates the remaining analytic inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The finite Abel-Plana decomposition on the right half-plane gives the real
axis component required by the Binet principal-log coherence package. -/
theorem Complex.gammaBinetPrincipalLogCoherence_realAxis_of_rightHalfPlaneFinite
    (hfinite :
      ∀ z : ℂ,
        0 < z.re →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) :
    ∀ x : ℝ,
      0 < x →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
            Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ) :=
  fun x hx => hfinite (x : ℂ) (Eq.subst
    (motive := fun r : ℝ => 0 < r)
    (Complex.ofReal_re x).symm
    hx)

/-- The open right half-plane gives the local neighborhood component of the
Binet principal-log coherence package from a global right-half-plane finite
Abel-Plana decomposition. -/
theorem Complex.gammaBinetPrincipalLogCoherence_local_of_rightHalfPlaneFinite
    (hfinite :
      ∀ z : ℂ,
        0 < z.re →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) :
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
                  Complex.binetAbelPlanaFiniteContourRemainder N y) := by
  intro z hz
  have hpoint :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
              Complex.binetAbelPlanaFiniteContourRemainder N z :=
    hfinite z hz
  have hre_eventually : ∀ᶠ y : ℂ in 𝓝 z, 0 < y.re :=
    (Complex.continuous_re.continuousAt.eventually
      (IsOpen.mem_nhds isOpen_Ioi hz))
  have hlocal :
      ∀ᶠ y : ℂ in 𝓝 z,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
            Complex.binetAbelPlanaFiniteMainTerm N y +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                Complex.binetAbelPlanaFiniteContourRemainder N y :=
    hre_eventually.mono
      (fun y hy => hfinite y hy)
  exact ⟨hpoint, hlocal⟩

/-- A global right-half-plane finite Abel-Plana decomposition and the Gamma
branch-cut theorem assemble the full Binet principal-log coherence package. -/
theorem Complex.gammaBinetPrincipalLogCoherence_of_rightHalfPlaneFinite
    (hGamma_slit :
      ∀ z : ℂ, 0 < z.re → Complex.Gamma z ∈ Complex.slitPlane)
    (hfinite :
      ∀ z : ℂ,
        0 < z.re →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) :
    Complex.gammaBinetPrincipalLogCoherence :=
  ⟨hGamma_slit,
    Complex.gammaBinetPrincipalLogCoherence_realAxis_of_rightHalfPlaneFinite
      hfinite,
    Complex.gammaBinetPrincipalLogCoherence_local_of_rightHalfPlaneFinite
      hfinite⟩

end

end LFunctions
end Boundary
