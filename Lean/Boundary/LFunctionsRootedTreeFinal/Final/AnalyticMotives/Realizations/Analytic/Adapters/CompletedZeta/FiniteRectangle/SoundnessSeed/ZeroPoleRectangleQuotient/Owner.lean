import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.FormalSumClass.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRectangleRepresentative.Owner

/-!
# Zero-pole rectangle-certified ambient quotient class

This file names the ambient `TraceCorQQuotient` class represented by the
rectangle-certified zero-pole residue candidate.

The quotient class itself is not assigned a canonical certificate ledger here;
certificate accounting remains attached to the explicit representative and
candidate.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The ambient quotient class represented by the rectangle-certified zero-pole candidate. -/
def completedZetaZeroPoleResidueRectangleTraceCorQQuotient
    (R : ℝ) :
    TraceCorQQuotient :=
  TraceCorQQuotient.ofCandidate
    (completedZetaZeroPoleResidueRectangleTraceCorQCandidate R)

/-- The rectangle-certified quotient is represented by its explicit candidate. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQQuotient_eq_ofCandidate
    (R : ℝ) :
    completedZetaZeroPoleResidueRectangleTraceCorQQuotient R =
      TraceCorQQuotient.ofCandidate
        (completedZetaZeroPoleResidueRectangleTraceCorQCandidate R) :=
  rfl

/-- The rectangle-certified quotient is the ambient class of its typed representative. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQQuotient_eq_representative_ambientClass
    (R : ℝ) :
    completedZetaZeroPoleResidueRectangleTraceCorQQuotient R =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R).ambientClass :=
  rfl

/-- The rectangle-certified quotient is also the direct class of the raw singleton formal sum. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQQuotient_eq_ofFormalSum
    (R : ℝ) :
    completedZetaZeroPoleResidueRectangleTraceCorQQuotient R =
      TraceCorQQuotient.ofFormalSum
        (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).raw :=
  TraceCorQQuotient.ofCandidate_eq_ofFormalSum
    (completedZetaZeroPoleResidueRectangleTraceCorQCandidate R)

/--
The ambient quotient class has the same analytic soundness theorem as the
rectangle-certified generator that represents it.
-/
theorem completedZetaZeroPoleResidueRectangleTraceCorQQuotient_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleResidueRectangleTraceCorQHom_sound
    f hPhi hR

/--
The ambient quotient class is sound when the recorded rectangle height is
positive.
-/
theorem completedZetaZeroPoleResidueRectangleTraceCorQQuotient_sound_of_rectangleHeight
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ}
    (hT : 0 < (completedZetaZeroPoleFiniteSquareRectangle R).T) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleResidueRectangleTraceCorQQuotient_sound
    f hPhi hT

end AnalyticMotives
end LFunctions
end Boundary
