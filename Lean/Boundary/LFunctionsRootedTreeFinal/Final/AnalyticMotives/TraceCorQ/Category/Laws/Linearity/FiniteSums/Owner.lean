import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Instances.Owner

/-!
# Finite-sum linearity of trace-correspondence composition

Binary additivity and zero absorption make composition by a fixed trace
correspondence an additive monoid homomorphism.  This file exposes the finite
sum consequences needed by matrix composition in the analytic additive
envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Post-composition by a fixed trace correspondence is additive. -/
def TraceCorQHom.postCompAddMonoidHom
    {source middle target : TraceCorQObject}
    (tail : TraceCorQHom middle target) :
    TraceCorQHom source middle →+ TraceCorQHom source target where
  toFun := fun head =>
    TraceCorQHom.comp head tail
  map_zero' :=
    TraceCorQHom.std_zero_comp tail
  map_add' := fun left right =>
    TraceCorQHom.std_add_comp left right tail

/-- Pre-composition by a fixed trace correspondence is additive. -/
def TraceCorQHom.preCompAddMonoidHom
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle) :
    TraceCorQHom middle target →+ TraceCorQHom source target where
  toFun := fun tail =>
    TraceCorQHom.comp head tail
  map_zero' :=
    TraceCorQHom.std_comp_zero head
  map_add' := fun left right =>
    TraceCorQHom.std_comp_add head left right

/-- Trace composition distributes over a finite sum in the left input. -/
theorem TraceCorQHom.sum_comp
    {index : Type}
    {source middle target : TraceCorQObject}
    (indices : Finset index)
    (family : index → TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (indices.sum family)
      tail =
      indices.sum
        (fun index =>
          TraceCorQHom.comp
            (family index)
            tail) :=
  (TraceCorQHom.postCompAddMonoidHom tail).map_sum
    family
    indices

/-- Trace composition distributes over a finite sum in the right input. -/
theorem TraceCorQHom.comp_sum
    {index : Type}
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (indices : Finset index)
    (family : index → TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (indices.sum family) =
      indices.sum
        (fun index =>
          TraceCorQHom.comp
            head
            (family index)) :=
  (TraceCorQHom.preCompAddMonoidHom head).map_sum
    family
    indices

end AnalyticMotives
end LFunctions
end Boundary
