import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Owner

/-!
# Additive envelope objects

The triangulated homotopy-category construction needs an additive base
category with finite direct sums.  The analytic additive envelope has finite
families of certified trace presentations as objects.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Objects of the additive envelope are finite families of analytic trace objects. -/
abbrev TraceAnalyticAdditiveObject :=
  List TraceCorQObject

/-- The zero object of the additive envelope is the empty family. -/
def TraceAnalyticAdditiveObject.zero :
    TraceAnalyticAdditiveObject :=
  []

/-- Binary direct sum in the additive envelope is concatenation of families. -/
def TraceAnalyticAdditiveObject.directSum
    (left right : TraceAnalyticAdditiveObject) :
    TraceAnalyticAdditiveObject :=
  left ++ right

/-- A component object of a finite analytic trace family. -/
def TraceAnalyticAdditiveObject.component
    (object : TraceAnalyticAdditiveObject)
    (index : Fin object.length) :
    TraceCorQObject :=
  object.get index

/-- The zero additive object has no components. -/
theorem TraceAnalyticAdditiveObject.zero_length :
    TraceAnalyticAdditiveObject.zero.length =
      0 :=
  rfl

/-- Direct-sum length is the sum of the two family lengths. -/
theorem TraceAnalyticAdditiveObject.directSum_length
    (left right : TraceAnalyticAdditiveObject) :
    (TraceAnalyticAdditiveObject.directSum left right).length =
      left.length + right.length :=
  List.length_append left right

end AnalyticMotives
end LFunctions
end Boundary
