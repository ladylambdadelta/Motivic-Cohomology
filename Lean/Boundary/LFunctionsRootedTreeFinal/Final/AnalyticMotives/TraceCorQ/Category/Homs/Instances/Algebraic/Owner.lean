import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Module.MinimalAxioms
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Instances.Laws.Algebra.Owner

/-!
# Algebraic instances for typed trace-correspondence homs

This file packages the proved fixed-endpoint hom laws as standard Lean
`AddCommGroup` and `Rat`-module instances.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Each fixed typed trace-correspondence hom type is an additive commutative group. -/
instance traceCorQHomAddCommGroup
    {source target : TraceCorQObject} :
    AddCommGroup (TraceCorQHom source target) :=
  { AddGroup.ofLeftAxioms
      (fun first second third =>
        TraceCorQHom.std_add_assoc first second third)
      (fun hom =>
        TraceCorQHom.std_zero_add hom)
      (fun hom =>
        TraceCorQHom.std_neg_add_self hom) with
    add_comm := fun left right =>
      TraceCorQHom.std_add_comm left right }

/-- Each fixed typed trace-correspondence hom type is a rational module. -/
instance traceCorQHomRatModule
    {source target : TraceCorQObject} :
    Module Rat (TraceCorQHom source target) :=
  Module.ofMinimalAxioms
    (fun coefficient left right =>
      TraceCorQHom.std_smul_add coefficient left right)
    (fun leftCoefficient rightCoefficient hom =>
      TraceCorQHom.std_add_smul
        leftCoefficient
        rightCoefficient
        hom)
    (fun leftCoefficient rightCoefficient hom =>
      Eq.symm
        (TraceCorQHom.std_smul_smul
          leftCoefficient
          rightCoefficient
          hom))
    (fun hom =>
      TraceCorQHom.std_one_smul hom)

end AnalyticMotives
end LFunctions
end Boundary
