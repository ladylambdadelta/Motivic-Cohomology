import Boundary.LFunctions.ZetaExplicitFormulaBoundaryTransport

/-!
# Boundary explicit-formula residue bridge

This file owns the intermediate residue-shaped packaging between the zero-side
Krein form and the signed boundary transport form. It is intentionally narrow:
it records the ladder-shaped targets the explicit-formula argument needs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed residue boundary sum attached to an admissible probe. -/
noncomputable def zetaCompletedResidueBoundarySum (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedZeroKreinGram f

/-- The zero-side Krein form is the completed residue boundary sum. -/
theorem zetaCompletedZeroKreinGram_eq_residueBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      zetaCompletedResidueBoundarySum f := by
  rfl

/-- The residue boundary sum and the analytic prime/archimedean/correction boundary sum are
the same completed boundary scalar.

This is the residue-to-boundary comparison root.  It is the single complex owner theorem;
the real- and imaginary-part forms below are projections of this statement, not independent
analytic inputs. -/
theorem zetaCompletedResidueBoundarySum_eq_boundarySumAnalytic_owner
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedResidueBoundarySum f : ℂ) =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  sorry

/-- The residue boundary sum and the analytic prime/archimedean/correction boundary sum are
the same completed boundary scalar. -/
theorem zetaCompletedResidueBoundarySum_eq_boundarySumAnalytic
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedResidueBoundarySum f : ℂ) =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  exact zetaCompletedResidueBoundarySum_eq_boundarySumAnalytic_owner f

/-- The analytic boundary sum attached to a residue probe is real-valued. -/
theorem zetaCompletedResidueBoundarySum_boundarySumAnalytic_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaBoundarySumAnalytic f) = 0 := by
  calc
    Complex.im (zetaCompletedExplicitFormulaBoundarySumAnalytic f) =
        Complex.im ((zetaCompletedResidueBoundarySum f : ℂ)) := by
      exact congrArg Complex.im
        (zetaCompletedResidueBoundarySum_eq_boundarySumAnalytic f).symm
    _ = 0 := by
      exact Complex.ofReal_im (zetaCompletedResidueBoundarySum f)

/-- Real-part form of the residue-to-boundary comparison. -/
theorem zetaCompletedResidueBoundarySum_eq_boundarySumAnalytic_re
    (f : ZetaAdmissibleFunction) :
    zetaCompletedResidueBoundarySum f =
      Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
  calc
    zetaCompletedResidueBoundarySum f =
        Complex.re ((zetaCompletedResidueBoundarySum f : ℂ)) := by
      exact (Complex.ofReal_re (zetaCompletedResidueBoundarySum f)).symm
    _ = Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
      exact congrArg Complex.re
        (zetaCompletedResidueBoundarySum_eq_boundarySumAnalytic f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
