import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Owner

/-!
# Shifts in the additive analytic homotopy category

The additive analytic homotopy category inherits integer shifts from cochain
complexes in the analytic additive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The additive analytic homotopy category has integer shifts. -/
def TraceAnalyticAdditiveHomotopyCategory.hasShiftStructure :
    CategoryTheory.HasShift TraceAnalyticAdditiveHomotopyCategory ℤ :=
  inferInstance

/-- The integer shift functor on additive analytic homotopy motives. -/
def TraceAnalyticAdditiveHomotopyCategory.shiftFunctor
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory ⥤
      TraceAnalyticAdditiveHomotopyCategory :=
  CategoryTheory.shiftFunctor TraceAnalyticAdditiveHomotopyCategory degree

/-- The shifted additive analytic homotopy motive. -/
def TraceAnalyticAdditiveHomotopyCategory.shiftedObject
    (motive : TraceAnalyticAdditiveHomotopyCategory)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory :=
  (TraceAnalyticAdditiveHomotopyCategory.shiftFunctor degree).obj motive

/-- The shifted object is the object part of the additive homotopy shift functor. -/
theorem TraceAnalyticAdditiveHomotopyCategory.shiftedObject_eq
    (motive : TraceAnalyticAdditiveHomotopyCategory)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.shiftedObject motive degree =
      (TraceAnalyticAdditiveHomotopyCategory.shiftFunctor degree).obj motive :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
