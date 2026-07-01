import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Owner

/-!
# Operation instances for typed trace-correspondence homs

This file exposes the concrete fixed-endpoint hom operations through Lean's
standard operation classes.  No law-bearing algebraic class is introduced here.

Bridge laws for unfolding this notation live in `Category/Homs/Instances/Laws`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Standard zero notation for typed trace-correspondence homs. -/
instance traceCorQHomZero
    {source target : TraceCorQObject} :
    Zero (TraceCorQHom source target) where
  zero := TraceCorQHom.zero source target

/-- Standard addition notation for typed trace-correspondence homs. -/
instance traceCorQHomAdd
    {source target : TraceCorQObject} :
    Add (TraceCorQHom source target) where
  add := TraceCorQHom.add

/-- Standard negation notation for typed trace-correspondence homs. -/
instance traceCorQHomNeg
    {source target : TraceCorQObject} :
    Neg (TraceCorQHom source target) where
  neg := TraceCorQHom.neg

/-- Standard subtraction notation for typed trace-correspondence homs. -/
instance traceCorQHomSub
    {source target : TraceCorQObject} :
    Sub (TraceCorQHom source target) where
  sub := TraceCorQHom.sub

/-- Standard rational scalar notation for typed trace-correspondence homs. -/
instance traceCorQHomRatSMul
    {source target : TraceCorQObject} :
    SMul Rat (TraceCorQHom source target) where
  smul := TraceCorQHom.smul

end AnalyticMotives
end LFunctions
end Boundary
