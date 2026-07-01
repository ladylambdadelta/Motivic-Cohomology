import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.Morphisms.Linear.Owner

/-!
# Pointwise laws for linear presheaf morphisms

This owner proves identity and associativity laws for linear presheaf morphism
composition at the level of components.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQLinearPresheafMorphism

/-- Left identity for linear presheaf morphisms, componentwise. -/
theorem id_comp_component {F G : ContourCorQLinearPresheaf}
    (η : ContourCorQLinearPresheafMorphism F G)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (comp (id F) η).componentAt X a = η.componentAt X a :=
  rfl

/-- Right identity for linear presheaf morphisms, componentwise. -/
theorem comp_id_component {F G : ContourCorQLinearPresheaf}
    (η : ContourCorQLinearPresheafMorphism F G)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (comp η (id G)).componentAt X a = η.componentAt X a :=
  rfl

/-- Associativity for linear presheaf morphisms, componentwise. -/
theorem comp_assoc_component {F G H K : ContourCorQLinearPresheaf}
    (η : ContourCorQLinearPresheafMorphism F G)
    (θ : ContourCorQLinearPresheafMorphism G H)
    (κ : ContourCorQLinearPresheafMorphism H K)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (comp (comp η θ) κ).componentAt X a =
      (comp η (comp θ κ)).componentAt X a :=
  rfl

end ContourCorQLinearPresheafMorphism

end AnalyticMotives
end LFunctions
end Boundary
