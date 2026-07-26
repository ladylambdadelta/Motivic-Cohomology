import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.Base

/-!
# Paley-Wiener rapid decay for the explicit-formula transform

This downstream wrapper transports owner-level Laplace-transform rapid decay
to the completed explicit-formula transform.
-/

namespace Boundary
namespace LFunctions

open scoped Real

/-- A Laplace-transform vertical-strip decay certificate transports directly to
the completed explicit-formula transform. -/
theorem zetaPhi_hasVerticalStripDecayConstant_of_laplace
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) (C : ℝ)
    (hC :
      ZetaAdmissibleFunction.zetaLaplaceTransformHasVerticalStripDecayConstant
        f a b N C) :
    0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
  And.intro
    hC.1
    (fun z haz hzb =>
      let hphi :
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi f z =
            Boundary.zetaLaplaceTransform f.toZetaTestFunction' z :=
        congrFun
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi_eq_laplace f)
          z
      let hbound :
          ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
        hC.2 z (And.intro haz hzb)
      Eq.subst
        (motive := fun w : ℂ =>
          ‖w‖ ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)))
        hphi.symm
        hbound)

/-- Paley-Wiener rapid vertical-strip decay for the completed explicit-formula transform
`Phi_f`, projected as an existence statement for theorem consumers. -/
theorem zetaPhi_verticalStripRapidDecay_of_admissible_owner
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
  let I : ZetaAdmissibleFunction.ZetaPaleyWienerSupportInterval f :=
    ZetaAdmissibleFunction.canonicalZetaPaleyWienerSupportInterval f
  let C : ℝ :=
    zetaLaplaceTransform_supportInterval_decayConstant f I a b N
  let hC :
      ZetaAdmissibleFunction.zetaLaplaceTransformHasVerticalStripDecayConstant
        f a b N C :=
    And.intro
      (zetaLaplaceTransform_supportInterval_decayConstant_pos f I a b N)
      (zetaLaplaceTransform_supportInterval_decayConstant_bound f I a b N)
  let hPhi :
      0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi f z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
    zetaPhi_hasVerticalStripDecayConstant_of_laplace f a b N C hC
  ⟨C, hPhi.1, hPhi.2⟩

end LFunctions
end Boundary
