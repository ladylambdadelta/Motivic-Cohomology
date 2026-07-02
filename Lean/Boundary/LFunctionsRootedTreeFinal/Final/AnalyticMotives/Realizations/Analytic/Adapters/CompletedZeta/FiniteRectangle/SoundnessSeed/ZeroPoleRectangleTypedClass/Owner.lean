import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Ambient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRectangleQuotient.Owner

/-!
# Zero-pole rectangle-certified typed class bridge

This file identifies the typed rectangle-certified zero-pole residue hom with
its named representative and ambient quotient class.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The typed rectangle-certified hom is the class of its named representative. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHom_eq_ofRepresentative
    (R : ℝ) :
    completedZetaZeroPoleResidueRectangleTraceCorQHom R =
      TraceCorQHom.ofRepresentative
        (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R) :=
  rfl

/-- The ambient image of the typed rectangle-certified hom is the named ambient quotient. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHom_ambient
    (R : ℝ) :
    TraceCorQHom.ambient
      (completedZetaZeroPoleResidueRectangleTraceCorQHom R) =
      completedZetaZeroPoleResidueRectangleTraceCorQQuotient R :=
  rfl

/-- The ambient image of the named representative is the named ambient quotient. -/
theorem completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative_ambient
    (R : ℝ) :
    TraceCorQHom.ambient
      (TraceCorQHom.ofRepresentative
        (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R)) =
      completedZetaZeroPoleResidueRectangleTraceCorQQuotient R :=
  rfl

/--
The typed-class bridge preserves the same soundness theorem as the underlying
rectangle-certified quotient class.
-/
theorem completedZetaZeroPoleResidueRectangleTraceCorQTypedClass_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleResidueRectangleTraceCorQQuotient_sound
    f hPhi hR

/--
The typed-class bridge is sound when the recorded rectangle height is positive.
-/
theorem completedZetaZeroPoleResidueRectangleTraceCorQTypedClass_sound_of_rectangleHeight
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ}
    (hT : 0 < (completedZetaZeroPoleFiniteSquareRectangle R).T) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleResidueRectangleTraceCorQTypedClass_sound
    f hPhi hT

end AnalyticMotives
end LFunctions
end Boundary
