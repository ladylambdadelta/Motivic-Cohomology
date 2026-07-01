import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Morphisms.Owner

/-!
# Composition of trace transports

This file owns composition for analytic trace transports.

Composition is concatenation of certified rewrite traces, modulo the coherence
relations owned by the trace-rewrite layer.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The raw identity trace transport on a certified presentation. -/
def TraceTransport.id
    (object : TraceTransportObject) : TraceTransport :=
  {
    source := object
    target := object
    path := TraceRewritePath.id object.source
    path_source := rfl
    path_target := rfl
  }

/-- The identity trace transport starts at its object. -/
theorem TraceTransport.id_source
    (object : TraceTransportObject) :
    (TraceTransport.id object).source =
      object :=
  rfl

/-- The identity trace transport targets its object. -/
theorem TraceTransport.id_target
    (object : TraceTransportObject) :
    (TraceTransport.id object).target =
      object :=
  rfl

/-- The identity trace transport carries the identity rewrite path on the object's source. -/
theorem TraceTransport.id_path
    (object : TraceTransportObject) :
    (TraceTransport.id object).path =
      TraceRewritePath.id object.source :=
  rfl

/-- Compose raw trace transports by concatenating their rewrite paths. -/
def TraceTransport.comp
    (first second : TraceTransport) : TraceTransport :=
  {
    source := first.source
    target := second.target
    path := first.path.comp second.path
    path_source := first.path_source
    path_target := second.path_target
  }

/-- The source of a raw transport composition is the source of the first transport. -/
theorem TraceTransport.comp_source
    (first second : TraceTransport) :
    (TraceTransport.comp first second).source =
      first.source :=
  rfl

/-- The target of a raw transport composition is the target of the second transport. -/
theorem TraceTransport.comp_target
    (first second : TraceTransport) :
    (TraceTransport.comp first second).target =
      second.target :=
  rfl

/-- The path of a raw transport composition is the concatenated rewrite path. -/
theorem TraceTransport.comp_path
    (first second : TraceTransport) :
    (TraceTransport.comp first second).path =
      first.path.comp second.path :=
  rfl

/-- The identity trace transport path starts at the object's source expression. -/
theorem TraceTransport.id_path_source
    (object : TraceTransportObject) :
    (TraceTransport.id object).path.source =
      object.source :=
  rfl

/-- The identity trace transport path ends at the object's source expression. -/
theorem TraceTransport.id_path_target
    (object : TraceTransportObject) :
    (TraceTransport.id object).path.target =
      object.source :=
  rfl

/-- The source endpoint certificate of a raw composition is inherited from the first factor. -/
theorem TraceTransport.comp_path_source
    (first second : TraceTransport) :
    (TraceTransport.comp first second).path.source =
      first.source.source :=
  first.path_source

/-- The target endpoint certificate of a raw composition is inherited from the second factor. -/
theorem TraceTransport.comp_path_target
    (first second : TraceTransport) :
    (TraceTransport.comp first second).path.target =
      second.target.source :=
  second.path_target

end AnalyticMotives
end LFunctions
end Boundary
