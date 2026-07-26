import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.LogDerivativeFiniteFormula
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SlitPlaneDefinitions

/-!
# Binet principal-log coherence components

This file owns small assembly lemmas for the coherence package used by the
principal-log version of Binet's formula.  The branch-cut and finite
Abel-Plana inputs remain separate owner-level hypotheses until their
respective analytic constructors are applied.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

theorem Complex.GammaLocalSlitPlaneControl_owner :
    Complex.GammaLocalSlitPlaneControl := by
  intro z hz
  have hgamma_ne : Complex.Gamma z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hnot_pole : ∀ m : ℕ, z ≠ -m := by
    intro m hzm
    exact hgamma_ne ((Complex.Gamma_eq_zero_iff z).mpr ⟨m, hzm⟩)
  have hcont : ContinuousAt Complex.Gamma z :=
    (Complex.differentiableAt_Gamma z hnot_pole).continuousAt
  have hpreimage : Complex.Gamma ⁻¹' Complex.slitPlane ∈ 𝓝 z :=
    (Complex.isOpen_slitPlane.mem_nhds hz).preimage hcont
  rcases Metric.mem_nhds_iff.mp hpreimage with ⟨ε, hε, hball⟩
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro w hw
  have hdist : dist w z ≤ ε / 2 := Metric.mem_closedBall.mp hw
  exact hball (hdist.trans_lt (half_lt_self hε))

/-- The finite Abel-Plana owner supplies the right-half-plane finite
decomposition package. -/
theorem Complex.binetAbelPlanaRightHalfPlaneFiniteDecomposition_owner :
    Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition :=
  Complex.binetAbelPlanaFiniteFormula_openRightHalfPlane

/-- The finite Abel-Plana decomposition on the right half-plane gives the real
axis component required by the Binet principal-log coherence package. -/
theorem Complex.gammaBinetPrincipalLogCoherence_realAxis_of_rightHalfPlaneFinite
    (hfinite : Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition) :
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
    (hfinite : Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition) :
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
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite : Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition) :
    Complex.gammaBinetPrincipalLogCoherence :=
  ⟨hGamma_slit,
    Complex.gammaBinetPrincipalLogCoherence_realAxis_of_rightHalfPlaneFinite
      hfinite,
    Complex.gammaBinetPrincipalLogCoherence_local_of_rightHalfPlaneFinite
      hfinite⟩

/-- Owner-input constructor for the Binet principal-log coherence package. -/
theorem Complex.gammaBinetPrincipalLogCoherence_of_ownerInputs
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite : Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition) :
    Complex.gammaBinetPrincipalLogCoherence :=
  Complex.gammaBinetPrincipalLogCoherence_of_rightHalfPlaneFinite
    hGamma_slit
    hfinite

end

end LFunctions
end Boundary
