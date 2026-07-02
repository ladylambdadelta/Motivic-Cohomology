import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.FormalSumClass.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectangleRepresentative.Owner

/-!
# Zero-pole scheduled-rectangle channel ambient quotient class

This file names the ambient `TraceCorQQuotient` class represented by the
scheduled-rectangle channel candidate.

The quotient class itself is not assigned a canonical certificate ledger here;
certificate accounting remains attached to the explicit representative and
candidate.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The ambient quotient class represented by the scheduled-rectangle channel candidate. -/
def completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQQuotient :=
  TraceCorQQuotient.ofCandidate
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate
      f F h u)

/-- The scheduled-rectangle channel quotient is represented by its explicit candidate. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient_eq_ofCandidate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient f F h u =
      TraceCorQQuotient.ofCandidate
        (completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate
          f F h u) :=
  rfl

/-- The scheduled-rectangle channel quotient is the ambient class of its typed representative. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient_eq_representative_ambientClass
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient f F h u =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
        f F h u).ambientClass :=
  rfl

/-- The scheduled-rectangle channel quotient is also the direct class of the raw singleton. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient_eq_ofFormalSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient f F h u =
      TraceCorQQuotient.ofFormalSum
        (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
          f F h u).raw :=
  TraceCorQQuotient.ofCandidate_eq_ofFormalSum
    (completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate
      f F h u)

/--
The ambient quotient class has the same analytic soundness theorem as the
scheduled-rectangle channel generator that represents it.
-/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHom_sound
    f F h u

end AnalyticMotives
end LFunctions
end Boundary
