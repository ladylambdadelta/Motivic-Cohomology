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

/-- The analytic boundary sum attached to a residue probe is real-valued. -/
theorem zetaCompletedResidueBoundarySum_boundarySumAnalytic_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaBoundarySumAnalytic f) = 0 := by
  sorry

/-- Real-part form of the residue-to-boundary comparison. -/
theorem zetaCompletedResidueBoundarySum_eq_boundarySumAnalytic_re
    (f : ZetaAdmissibleFunction) :
    zetaCompletedResidueBoundarySum f =
      Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
  sorry

/-- The residue boundary sum and the analytic prime/archimedean/correction boundary sum are
the same completed boundary scalar.

This is the residue-to-boundary comparison root.  The final contour-shift file should use this
owner theorem rather than owning a duplicate vertical-transport comparison. -/
theorem zetaCompletedResidueBoundarySum_eq_boundarySumAnalytic
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedResidueBoundarySum f : ℂ) =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  have hre :
      zetaCompletedResidueBoundarySum f =
        Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic f) :=
    zetaCompletedResidueBoundarySum_eq_boundarySumAnalytic_re f
  have him :
      Complex.im (zetaCompletedExplicitFormulaBoundarySumAnalytic f) = 0 :=
    zetaCompletedResidueBoundarySum_boundarySumAnalytic_im_eq_zero f
  exact Complex.ext
    (by
      calc
        Complex.re ((zetaCompletedResidueBoundarySum f : ℂ)) =
            zetaCompletedResidueBoundarySum f := by
          exact Complex.ofReal_re (zetaCompletedResidueBoundarySum f)
        _ = Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic f) := hre)
    (by
      calc
        Complex.im ((zetaCompletedResidueBoundarySum f : ℂ)) = 0 := by
          exact Complex.ofReal_im (zetaCompletedResidueBoundarySum f)
        _ = Complex.im (zetaCompletedExplicitFormulaBoundarySumAnalytic f) := him.symm)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
