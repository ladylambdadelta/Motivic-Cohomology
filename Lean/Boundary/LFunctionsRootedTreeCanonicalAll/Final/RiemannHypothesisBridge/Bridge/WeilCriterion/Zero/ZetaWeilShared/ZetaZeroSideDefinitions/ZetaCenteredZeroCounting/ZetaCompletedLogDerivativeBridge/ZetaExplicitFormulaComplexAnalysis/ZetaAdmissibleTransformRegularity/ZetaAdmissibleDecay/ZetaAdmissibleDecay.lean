import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaAdmissiblePaleyWiener
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleInterpolation.ZetaAdmissibleSpectralModel.ZetaAdmissibleSpectralModel

/-!
# Boundary admissible decay data

This file exports the compact support and smoothness data carried by the
admissible test-function structure. It is the honest decay-side input currently
available for the Paley--Wiener model.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff

namespace ZetaAdmissibleFunction

/-- The admissible function has compact support. -/
theorem admissible_hasCompactSupport (f : ZetaAdmissibleFunction) :
    HasCompactSupport f := by
  exact hasCompactSupport f

/-- The admissible function is smooth on the logarithmic line. -/
theorem admissible_contDiff (f : ZetaAdmissibleFunction) : ContDiff ℝ ∞ f := by
  exact contDiff f

/-- The admissible function retains the underlying test-function carrier. -/
theorem admissible_toTestFunction (f : ZetaAdmissibleFunction) :
    f.toZetaTestFunction' = ZetaAdmissibleFunction.toZetaTestFunction' f := by
  rfl

/-- The admissible carrier keeps the underlying test function. -/
theorem admissible_carrier (f : ZetaAdmissibleFunction) :
    f.toZetaTestFunction' = ZetaAdmissibleFunction.toZetaTestFunction' f := by
  rfl

/-- Paley--Wiener rapid vertical-strip decay for the completed explicit-formula transform of
an admissible compactly supported smooth source. -/
theorem zetaPhi_verticalStripRapidDecay_of_admissible
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact zetaPhi_verticalStripRapidDecay_of_admissible_owner f a b N

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
