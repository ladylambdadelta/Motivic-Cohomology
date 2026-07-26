import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.CoherenceComponents
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlana
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.GammaSlitPlane

/-!
# Branch-correct Binet coherence

This file owns the unconditional Gamma/Binet coherence data in the branch
normalization supplied directly from Abel-Plana.  It avoids the stronger
principal-slit normalization, which is not the correct global right-half-plane
object.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The finite Abel-Plana decomposition supplies the global Binet branch
exponential identity. -/
theorem Complex.binetLogGammaBranchExponentialControl_of_rightHalfPlaneFinite
    (hfinite : Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition) :
    Complex.BinetLogGammaBranchExponentialControl :=
  fun z hz =>
    Complex.exp_binetLogGammaBranch_eq_Gamma_from_AbelPlana
      z
      hz
      (hfinite z hz)

/-- Owner theorem for the branch-correct Binet exponential identity. -/
theorem Complex.binetLogGammaBranchExponentialControl_owner :
    Complex.BinetLogGammaBranchExponentialControl :=
  Complex.binetLogGammaBranchExponentialControl_of_rightHalfPlaneFinite
    Complex.binetAbelPlanaRightHalfPlaneFiniteDecomposition_owner

/- The norm transport used by sectorial estimates is branch-correct: it follows
   from the exponential identity and does not require the principal logarithm
   of Gamma to be globally coherent. -/
theorem Complex.log_norm_Gamma_eq_binetLogGammaBranch_re_of_exponentialControl
    (hExp : Complex.BinetLogGammaBranchExponentialControl)
    {z : ℂ} (hz : 0 < z.re) :
    Real.log ‖Complex.Gamma z‖ =
      (Complex.binetLogGammaBranch z).re := by
  have hgamma :
      Complex.Gamma z = Complex.exp (Complex.binetLogGammaBranch z) :=
    (hExp z hz).symm
  have hnorm :
      ‖Complex.Gamma z‖ =
        Real.exp (Complex.binetLogGammaBranch z).re := by
    exact Eq.trans
      (congrArg norm hgamma)
      (Eq.trans
        Complex.norm_eq_abs
        (Complex.abs_exp (Complex.binetLogGammaBranch z)))
  exact Eq.trans
    (congrArg Real.log hnorm)
    (Real.log_exp (Complex.binetLogGammaBranch z).re)

/- Canonical owner specialization for the unconditional Abel--Plana package. -/
theorem Complex.log_norm_Gamma_eq_binetLogGammaBranch_re_owner
    {z : ℂ} (hz : 0 < z.re) :
    Real.log ‖Complex.Gamma z‖ =
      (Complex.binetLogGammaBranch z).re :=
  Complex.log_norm_Gamma_eq_binetLogGammaBranch_re_of_exponentialControl
    Complex.binetLogGammaBranchExponentialControl_owner hz

/-- Finite Abel-Plana data assemble the branch-correct Binet coherence
package. -/
theorem Complex.binetBranchLogGammaCoherence_of_rightHalfPlaneFinite
    (hfinite : Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition) :
    Complex.binetBranchLogGammaCoherence :=
  And.intro
    (Complex.binetLogGammaBranchExponentialControl_of_rightHalfPlaneFinite
      hfinite)
    (And.intro
      (Complex.gammaBinetPrincipalLogCoherence_realAxis_of_rightHalfPlaneFinite
        hfinite)
      (Complex.gammaBinetPrincipalLogCoherence_local_of_rightHalfPlaneFinite
        hfinite))

/-- Owner theorem for the branch-correct Binet coherence package. -/
theorem Complex.binetBranchLogGammaCoherence_owner :
  Complex.binetBranchLogGammaCoherence :=
  Complex.binetBranchLogGammaCoherence_of_rightHalfPlaneFinite
    Complex.binetAbelPlanaRightHalfPlaneFiniteDecomposition_owner

/- The corrected carrier-level package exposes the only slit-plane input used
   by scheduled probes: positive real centres with a proved closed
   neighbourhood.  The global Gamma nonvanishing and Abel--Plana identities
   remain separate components. -/
def Complex.BinetPositiveRealProbeCarrierControl : Prop :=
  Complex.BinetLogGammaBranchExponentialControl ∧
  Complex.GammaPositiveRealProbeSlitPlaneAndNonzeroControl ∧
  Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition

theorem Complex.binetCarrierBranchCoherence_owner :
    Complex.BinetCarrierBranchCoherence := by
  exact ⟨Complex.binetLogGammaBranchExponentialControl_owner,
    ⟨Complex.binetAbelPlanaRightHalfPlaneFiniteDecomposition_owner,
      Complex.GammaLocalSlitPlaneControl_owner⟩⟩

theorem Complex.binetRightHalfPlaneCarrierControl_owner :
    Complex.BinetRightHalfPlaneCarrierControl := by
  exact ⟨Complex.binetLogGammaBranchExponentialControl_owner,
    ⟨Complex.Gamma_openRightHalfPlane_nonzero_owner,
      ⟨Complex.GammaLocalSlitPlaneControl_owner,
      Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition_owner⟩⟩⟩

theorem Complex.binetPositiveRealProbeCarrierControl_owner :
    Complex.BinetPositiveRealProbeCarrierControl := by
  exact ⟨Complex.binetLogGammaBranchExponentialControl_owner,
    ⟨Complex.GammaPositiveRealProbeSlitPlaneAndNonzeroControl_owner,
      Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition_owner⟩⟩

end

end LFunctions
end Boundary
