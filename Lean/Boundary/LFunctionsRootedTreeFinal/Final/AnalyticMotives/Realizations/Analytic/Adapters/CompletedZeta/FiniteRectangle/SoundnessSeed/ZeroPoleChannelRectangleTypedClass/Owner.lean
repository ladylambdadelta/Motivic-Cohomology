import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Ambient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectangleQuotient.Owner

/-!
# Zero-pole scheduled-rectangle channel typed class bridge

This file identifies the typed scheduled-rectangle channel hom with its named
representative and ambient quotient class.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The typed scheduled-rectangle channel hom is the class of its named representative. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHom_eq_ofRepresentative
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelScheduledRectangleTraceCorQHom f F h u =
      TraceCorQHom.ofRepresentative
        (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
          f F h u) :=
  rfl

/-- The ambient image of the typed scheduled-rectangle channel hom is the named quotient. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHom_ambient
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHom.ambient
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHom f F h u) =
      completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient f F h u :=
  rfl

/-- The ambient image of the named representative is the named quotient. -/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative_ambient
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHom.ambient
      (TraceCorQHom.ofRepresentative
        (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
          f F h u)) =
      completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient f F h u :=
  rfl

/--
The typed-class bridge preserves the same soundness theorem as the underlying
scheduled-rectangle quotient class.
-/
theorem completedZetaZeroPoleChannelScheduledRectangleTraceCorQTypedClass_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient_sound
    f F h u

end AnalyticMotives
end LFunctions
end Boundary
