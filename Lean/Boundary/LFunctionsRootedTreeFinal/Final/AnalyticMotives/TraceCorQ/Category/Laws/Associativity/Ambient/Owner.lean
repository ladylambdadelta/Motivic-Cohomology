import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Owner

/-!
# Ambient associativity for typed trace-correspondence composition

This file proves that typed hom composition is associative after applying the
ambient quotient forgetful map.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Expand the ambient class of a left-associated typed composite. -/
theorem TraceCorQHom.ambient_comp_assoc_left_expansion
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHom first second)
    (middle : TraceCorQHom second third)
    (right : TraceCorQHom third fourth) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        (TraceCorQHom.comp left middle)
        right) =
      TraceCorQQuotient.comp
        (TraceCorQQuotient.comp
          (TraceCorQHom.ambient left)
          (TraceCorQHom.ambient middle))
        (TraceCorQHom.ambient right) :=
  Eq.trans
    (TraceCorQHom.ambient_comp
      (TraceCorQHom.comp left middle)
      right)
    (congrArg
      (fun leftClass =>
        TraceCorQQuotient.comp
          leftClass
          (TraceCorQHom.ambient right))
      (TraceCorQHom.ambient_comp left middle))

/-- Expand the ambient class of a right-associated typed composite. -/
theorem TraceCorQHom.ambient_comp_assoc_right_expansion
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHom first second)
    (middle : TraceCorQHom second third)
    (right : TraceCorQHom third fourth) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        left
        (TraceCorQHom.comp middle right)) =
      TraceCorQQuotient.comp
        (TraceCorQHom.ambient left)
        (TraceCorQQuotient.comp
          (TraceCorQHom.ambient middle)
          (TraceCorQHom.ambient right)) :=
  Eq.trans
    (TraceCorQHom.ambient_comp
      left
      (TraceCorQHom.comp middle right))
    (congrArg
      (fun rightClass =>
        TraceCorQQuotient.comp
          (TraceCorQHom.ambient left)
          rightClass)
      (TraceCorQHom.ambient_comp middle right))

/-- Typed hom composition is associative after forgetting to the ambient quotient. -/
theorem TraceCorQHom.ambient_comp_assoc
    {first second third fourth : TraceCorQObject}
    (left : TraceCorQHom first second)
    (middle : TraceCorQHom second third)
    (right : TraceCorQHom third fourth) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        (TraceCorQHom.comp left middle)
        right) =
      TraceCorQHom.ambient
        (TraceCorQHom.comp
          left
          (TraceCorQHom.comp middle right)) :=
  Eq.trans
    (TraceCorQHom.ambient_comp_assoc_left_expansion
      left
      middle
      right)
    (Eq.trans
      (TraceCorQQuotient.comp_assoc
        (TraceCorQHom.ambient left)
        (TraceCorQHom.ambient middle)
        (TraceCorQHom.ambient right))
      (Eq.symm
        (TraceCorQHom.ambient_comp_assoc_right_expansion
          left
          middle
          right)))

end AnalyticMotives
end LFunctions
end Boundary
