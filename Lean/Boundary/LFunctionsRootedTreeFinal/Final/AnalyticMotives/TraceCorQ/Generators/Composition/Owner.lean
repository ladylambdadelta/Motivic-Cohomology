import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Generators.Owner

/-!
# Composition of trace-correspondence generators

This file exposes identity and composition for raw `TraceCorQ` generators.

A generator is a raw trace transport, so these operations are the transport
identity and transport composition under the `TraceCorQGenerator` name.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The identity trace-correspondence generator on an object. -/
def TraceCorQGenerator.id
    (object : TraceCorQObject) :
    TraceCorQGenerator :=
  TraceTransport.id object

/-- Compose trace-correspondence generators by composing their transports. -/
def TraceCorQGenerator.comp
    (first second : TraceCorQGenerator) :
    TraceCorQGenerator :=
  TraceTransport.comp first second

/-- The identity trace-correspondence generator starts at its object. -/
theorem TraceCorQGenerator.id_source
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).source =
      object :=
  TraceTransport.id_source object

/-- The identity trace-correspondence generator targets its object. -/
theorem TraceCorQGenerator.id_target
    (object : TraceCorQObject) :
    (TraceCorQGenerator.id object).target =
      object :=
  TraceTransport.id_target object

/-- Composition of trace-correspondence generators starts at the first source. -/
theorem TraceCorQGenerator.comp_source
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).source =
      first.source :=
  TraceTransport.comp_source first second

/-- Composition of trace-correspondence generators targets the second target. -/
theorem TraceCorQGenerator.comp_target
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).target =
      second.target :=
  TraceTransport.comp_target first second

/-- Composition of trace-correspondence generators concatenates rewrite paths. -/
theorem TraceCorQGenerator.comp_path
    (first second : TraceCorQGenerator) :
    (TraceCorQGenerator.comp first second).path =
      first.path.comp second.path :=
  TraceTransport.comp_path first second

end AnalyticMotives
end LFunctions
end Boundary
