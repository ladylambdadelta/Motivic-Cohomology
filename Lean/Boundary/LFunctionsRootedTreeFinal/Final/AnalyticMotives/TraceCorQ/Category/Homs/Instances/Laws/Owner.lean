import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Instances.Owner

/-!
# Operation-instance bridge laws for typed trace-correspondence homs

This file records that standard operation notation unfolds to the concrete
fixed-endpoint hom operations owned earlier in the tree.

Standard-notation wrappers for proved algebraic laws live in
`Category/Homs/Instances/Laws/Algebra`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Standard zero notation unfolds to the concrete typed hom zero. -/
theorem TraceCorQHom.inst_zero_eq
    (source target : TraceCorQObject) :
    (0 : TraceCorQHom source target) =
      TraceCorQHom.zero source target :=
  rfl

/-- Standard addition notation unfolds to concrete typed hom addition. -/
theorem TraceCorQHom.inst_add_eq
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    left + right =
      TraceCorQHom.add left right :=
  rfl

/-- Standard negation notation unfolds to concrete typed hom negation. -/
theorem TraceCorQHom.inst_neg_eq
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    -hom =
      TraceCorQHom.neg hom :=
  rfl

/-- Standard subtraction notation unfolds to concrete typed hom subtraction. -/
theorem TraceCorQHom.inst_sub_eq
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    left - right =
      TraceCorQHom.sub left right :=
  rfl

/-- Standard rational scalar notation unfolds to concrete typed hom scalar multiplication. -/
theorem TraceCorQHom.inst_smul_eq
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    coefficient • hom =
      TraceCorQHom.smul coefficient hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
