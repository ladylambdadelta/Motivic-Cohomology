import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.Owner

/-!
# Paley-Wiener rapid decay for the explicit-formula transform

This downstream wrapper transports owner-level Laplace-transform rapid decay
to the completed explicit-formula transform.
-/

namespace Boundary
namespace LFunctions

open scoped Real

/-- Paley-Wiener rapid vertical-strip decay for the completed explicit-formula transform
`Phi_f`, projected as an existence statement for theorem consumers. -/
theorem zetaPhi_verticalStripRapidDecay_of_admissible_owner
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  have hbase :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
    zetaLaplaceTransform_verticalStripRapidDecay_of_compactSupport_smooth
      f a b N
  match hbase with
  | ⟨C, hCpos, hboundBase⟩ =>
      exact ⟨C, hCpos, fun z haz hzb =>
        let hphi :
            zetaCompletedExplicitFormulaPhi f z =
              Boundary.zetaLaplaceTransform f.toZetaTestFunction' z := by
          exact congrFun (zetaCompletedExplicitFormulaPhi_eq_laplace f) z
        let hbound :
            ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
              ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
          hboundBase z haz hzb
        Eq.subst
          (motive := fun w : ℂ =>
            ‖w‖ ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)))
          hphi.symm
          hbound⟩

end LFunctions
end Boundary
