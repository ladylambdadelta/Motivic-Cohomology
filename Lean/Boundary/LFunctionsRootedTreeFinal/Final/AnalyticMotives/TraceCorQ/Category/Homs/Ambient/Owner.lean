import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Classes.Owner

/-!
# Ambient quotient map for typed hom classes

This file owns the well-defined forgetful map from typed hom classes to the
ambient untyped quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Forget a typed hom class to its ambient quotient class. -/
def TraceCorQHom.ambient
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQQuotient :=
  Quotient.liftOn
    hom
    TraceCorQHomRepresentative.ambientClass
    (fun left right relation =>
      TraceCorQQuotient.sound relation)

/-- The ambient map agrees with the raw candidate of a representative. -/
theorem TraceCorQHom.ambient_ofRepresentative
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.ofRepresentative representative) =
      representative.ambientClass :=
  rfl

/-- The ambient map sends a typed formal-sum class to its raw formal-sum class. -/
theorem TraceCorQHom.ambient_ofFormalSum
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.ofFormalSum formalSum) =
      TraceCorQQuotient.ofFormalSum formalSum.raw :=
  rfl

/-- The ambient map sends a typed zero hom to the ambient zero quotient class. -/
theorem TraceCorQHom.ambient_zero
    (source target : TraceCorQObject) :
    TraceCorQHom.ambient
      (TraceCorQHom.zero source target) =
      TraceCorQQuotient.zero :=
  rfl

/-- The ambient map sends a typed singleton hom to the ambient singleton class. -/
theorem TraceCorQHom.ambient_singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom.ambient
      (TraceCorQHom.singleton
        source
        target
        coefficient
        generator
        source_eq
        target_eq) =
      TraceCorQQuotient.singleton coefficient generator :=
  rfl

/-- Ambient equality reflects equality of typed hom classes with fixed endpoints. -/
theorem TraceCorQHom.eq_of_ambient_eq
    {source target : TraceCorQObject}
    {left right : TraceCorQHom source target}
    (ambient_eq :
      TraceCorQHom.ambient left =
        TraceCorQHom.ambient right) :
    left = right :=
  Quotient.inductionOn₂
    left
    right
    (fun leftRepresentative rightRepresentative representative_ambient_eq =>
      TraceCorQHom.sound
        (TraceCorQHomRelation.ofAmbientEq representative_ambient_eq))
    ambient_eq

end AnalyticMotives
end LFunctions
end Boundary
