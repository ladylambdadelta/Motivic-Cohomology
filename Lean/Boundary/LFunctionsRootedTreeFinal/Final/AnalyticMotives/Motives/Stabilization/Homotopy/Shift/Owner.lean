import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Homotopy.Owner

/-!
# Shifts in the analytic trace homotopy category

The homotopy category inherits the integer shift of cochain complexes.  This is
the visible suspension/desuspension operation used by the later triangulated
analytic-motive category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic trace homotopy category has integer shifts. -/
def TraceAnalyticHomotopyCategory.hasShiftStructure :
    CategoryTheory.HasShift TraceAnalyticHomotopyCategory ℤ :=
  inferInstance

/-- The shift functor on analytic trace homotopy motives. -/
def TraceAnalyticHomotopyCategory.shiftFunctor
    (degree : ℤ) :
    TraceAnalyticHomotopyCategory ⥤ TraceAnalyticHomotopyCategory :=
  CategoryTheory.shiftFunctor TraceAnalyticHomotopyCategory degree

/-- The shifted analytic trace homotopy motive. -/
def TraceAnalyticHomotopyCategory.shiftedObject
    (motive : TraceAnalyticHomotopyCategory)
    (degree : ℤ) :
    TraceAnalyticHomotopyCategory :=
  (TraceAnalyticHomotopyCategory.shiftFunctor degree).obj motive

/-- The shifted object is the object part of the shift functor. -/
theorem TraceAnalyticHomotopyCategory.shiftedObject_eq
    (motive : TraceAnalyticHomotopyCategory)
    (degree : ℤ) :
    TraceAnalyticHomotopyCategory.shiftedObject motive degree =
      (TraceAnalyticHomotopyCategory.shiftFunctor degree).obj motive :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
