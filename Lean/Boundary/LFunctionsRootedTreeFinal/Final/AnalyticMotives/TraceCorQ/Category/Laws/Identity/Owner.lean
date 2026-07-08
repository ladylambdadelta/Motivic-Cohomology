import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Singleton.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Typed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Full.Owner

/-!
# Identity laws for typed trace-correspondence composition

This aggregate owns the identity-law lane for typed trace correspondences:
singleton identities, finite formal-sum identities, typed quotient identities,
and full unit normalization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity aggregate: left identity holds for typed singletons after ambient forgetful map. -/
theorem TraceCorQCategoryIdentity.ambient_left_id_singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        (TraceCorQHom.id source)
        (TraceCorQHom.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq)) =
      TraceCorQHom.ambient
        (TraceCorQHom.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq) :=
  TraceCorQHom.ambient_left_id_singleton
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- Identity aggregate: right identity holds for typed singletons after ambient forgetful map. -/
theorem TraceCorQCategoryIdentity.ambient_right_id_singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        (TraceCorQHom.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq)
        (TraceCorQHom.id target)) =
      TraceCorQHom.ambient
        (TraceCorQHom.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq) :=
  TraceCorQHom.ambient_right_id_singleton
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- Identity aggregate: left identity holds for typed formal sums after ambient forgetful map. -/
theorem TraceCorQCategoryIdentity.ambient_left_id_ofFormalSum
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        (TraceCorQHom.id source)
        (TraceCorQHom.ofFormalSum formalSum)) =
      TraceCorQHom.ambient
        (TraceCorQHom.ofFormalSum formalSum) :=
  TraceCorQHom.ambient_left_id_ofFormalSum
    formalSum

/-- Identity aggregate: right identity holds for typed formal sums after ambient forgetful map. -/
theorem TraceCorQCategoryIdentity.ambient_right_id_ofFormalSum
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp
        (TraceCorQHom.ofFormalSum formalSum)
        (TraceCorQHom.id target)) =
      TraceCorQHom.ambient
        (TraceCorQHom.ofFormalSum formalSum) :=
  TraceCorQHom.ambient_right_id_ofFormalSum
    formalSum

/-- Identity aggregate: representatives reduce to formal-sum ambient classes. -/
theorem TraceCorQCategoryIdentity.representative_ambientClass_eq_ofFormalSum
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    representative.ambientClass =
      TraceCorQQuotient.ofFormalSum representative.formalSum.raw :=
  TraceCorQHomRepresentative.ambientClass_eq_ofFormalSum
    representative

/-- Identity aggregate: left identity for typed homs. -/
theorem TraceCorQCategoryIdentity.left_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
      (TraceCorQHom.id source)
      hom =
      hom :=
  TraceCorQHom.left_id
    hom

/-- Identity aggregate: right identity for typed homs. -/
theorem TraceCorQCategoryIdentity.right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
      hom
      (TraceCorQHom.id target) =
      hom :=
  TraceCorQHom.right_id
    hom

/-- Identity aggregate: the identity composed with itself is the identity. -/
theorem TraceCorQCategoryIdentity.id_comp_id
    (object : TraceCorQObject) :
    TraceCorQHom.comp
      (TraceCorQHom.id object)
      (TraceCorQHom.id object) =
      TraceCorQHom.id object :=
  TraceCorQHom.id_comp_id
    object

/-- Identity aggregate: a hom with both endpoint identities attached normalizes. -/
theorem TraceCorQCategoryIdentity.left_id_right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
      (TraceCorQHom.id source)
      (TraceCorQHom.comp hom (TraceCorQHom.id target)) =
      hom :=
  TraceCorQHom.left_id_right_id
    hom

/-- Identity aggregate: left-associated endpoint identities also normalize. -/
theorem TraceCorQCategoryIdentity.left_id_comp_right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
      (TraceCorQHom.comp (TraceCorQHom.id source) hom)
      (TraceCorQHom.id target) =
      hom :=
  TraceCorQHom.left_id_comp_right_id
    hom

end AnalyticMotives
end LFunctions
end Boundary
