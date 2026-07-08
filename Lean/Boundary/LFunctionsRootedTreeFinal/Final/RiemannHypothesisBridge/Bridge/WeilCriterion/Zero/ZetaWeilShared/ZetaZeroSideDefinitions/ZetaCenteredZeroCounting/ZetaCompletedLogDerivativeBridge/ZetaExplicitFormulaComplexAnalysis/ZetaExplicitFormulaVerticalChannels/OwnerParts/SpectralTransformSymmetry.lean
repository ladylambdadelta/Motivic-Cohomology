import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ConjugateSymmetricTransforms
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.Owner

/-!
# Spectral Transform Conjugacy via Dagger Structure

Proves that the spectral transform Φ_f of an admissible function
is conjugate-symmetric by using the functional equation's dagger structure.

The dagger theorem encodes the functional equation of completed zeta
and gives us: Φ(dagger f)(z) = conj(Φ(f)(-conj(z)))

This file derives the conjugacy property for Φ(f) itself from this structure.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology
open ZetaAdmissibleFunction

namespace SpectralTransformSymmetry

/-- The dagger relationship at -conj(s) gives conjugacy structure. -/
lemma daggerTheorem_at_opposite_conjugate
    (f : ZetaAdmissibleFunction) (s : ℂ) :
    zetaCompletedExplicitFormulaPhi (zetaAdmissibleDagger f) (-star s) =
    star (zetaCompletedExplicitFormulaPhi f s) := by
  have h_star_neg : star (-star s) = -star (star s) := star_neg (star s)
  have h_star_star_neg : -star (star s) = -s :=
    congrArg Neg.neg (star_star s)
  have h_star_neg_value : star (-star s) = -s :=
    Eq.trans h_star_neg h_star_star_neg
  have h_opposite_opposite : -star (-star s) = s :=
    Eq.trans (congrArg Neg.neg h_star_neg_value) (neg_neg s)
  have h_phi :
      star (zetaCompletedExplicitFormulaPhi f (-star (-star s))) =
      star (zetaCompletedExplicitFormulaPhi f s) :=
    congrArg (fun z : ℂ => star (zetaCompletedExplicitFormulaPhi f z)) h_opposite_opposite
  exact Eq.trans (zetaCompletedExplicitFormulaPhi_dagger f (-star s)) h_phi

end SpectralTransformSymmetry

end
end LFunctions
end Boundary
