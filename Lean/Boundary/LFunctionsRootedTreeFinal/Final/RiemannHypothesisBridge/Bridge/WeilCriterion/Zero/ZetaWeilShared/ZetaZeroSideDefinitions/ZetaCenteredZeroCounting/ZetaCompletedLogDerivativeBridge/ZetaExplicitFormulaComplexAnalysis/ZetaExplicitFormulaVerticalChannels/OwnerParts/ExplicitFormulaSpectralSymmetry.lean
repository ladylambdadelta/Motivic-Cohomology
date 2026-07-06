import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ConjugateSymmetricTransforms
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleInterpolation.ZetaAdmissibleProbe.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.Owner

/-!
# Explicit Formula Spectral Symmetry

This file records elementary algebraic spectral-transform identities.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology
open ZetaAdmissibleFunction

namespace ExplicitFormulaSymmetry

/-- The spectral transform of the zero admissible function is zero. -/
theorem spectralTransform_zero :
    zetaCompletedExplicitFormulaPhi (0 : ZetaAdmissibleFunction) = fun _ => 0 := by
  exact
    funext
      (fun z : ℂ =>
        zetaCompletedExplicitFormulaPhi_zero z)

/-- The spectral transform is linear: Φ_(f+g) = Φ_f + Φ_g -/
theorem spectralTransform_add (f g : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi (f + g) =
    fun s => zetaCompletedExplicitFormulaPhi f s +
             zetaCompletedExplicitFormulaPhi g s := by
  have hpoint :
      ∀ t : ℝ,
        (f + g).toZetaTestFunction' t =
          (f.toZetaTestFunction' + g.toZetaTestFunction') t := by
    intro t
    calc
      (f + g).toZetaTestFunction' t =
          (f + g) t := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply (f + g) t
      _ = f t + g t := by
        exact ZetaAdmissibleFunction.add_apply f g t
      _ = f.toZetaTestFunction' t + g.toZetaTestFunction' t := by
        exact congrArg₂
          (fun u v : ℂ => u + v)
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply f t).symm
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply g t).symm
      _ = (f.toZetaTestFunction' + g.toZetaTestFunction') t := by
        exact Eq.refl _
  exact
    funext
      (fun z : ℂ =>
        calc
          zetaCompletedExplicitFormulaPhi (f + g) z =
              Boundary.zetaLaplaceTransform (f + g).toZetaTestFunction' z := by
            exact congrFun (zetaCompletedExplicitFormulaPhi_eq_laplace (f + g)) z
          _ =
              Boundary.zetaLaplaceTransform
                (f.toZetaTestFunction' + g.toZetaTestFunction') z := by
            exact zetaLaplaceTransform_congr_apply_ownerAdmissibleProbe
              hpoint z
          _ =
              Boundary.zetaLaplaceTransform f.toZetaTestFunction' z +
                Boundary.zetaLaplaceTransform g.toZetaTestFunction' z := by
            exact Boundary.zetaLaplaceTransform_add
              f.toZetaTestFunction'
              g.toZetaTestFunction'
              z
              (integrable_laplaceKernel_at f z)
              (integrable_laplaceKernel_at g z)
          _ =
              zetaCompletedExplicitFormulaPhi f z +
                zetaCompletedExplicitFormulaPhi g z := by
            exact congrArg₂
              (fun u v : ℂ => u + v)
              (congrFun (zetaCompletedExplicitFormulaPhi_eq_laplace f).symm z)
              (congrFun (zetaCompletedExplicitFormulaPhi_eq_laplace g).symm z))

end ExplicitFormulaSymmetry

end
end LFunctions
end Boundary
