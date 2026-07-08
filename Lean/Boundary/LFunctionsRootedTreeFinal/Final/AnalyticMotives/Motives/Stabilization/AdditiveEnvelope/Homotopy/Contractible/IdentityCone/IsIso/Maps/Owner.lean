import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Contractible.Owner

/-!
# Maps from an isomorphism cone to an identity cone

This file constructs the two concrete mapping-cone maps associated to an
isomorphism of additive analytic cochain complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveHomotopyCategory

/-- The commutative square used to map the cone of an isomorphism to the cone
of the identity on its target. -/
theorem mappingConeIsoToIdentityCone_comm
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    hom ≫ 𝟙 target = hom ≫ 𝟙 target :=
  rfl

/-- The commutative square used to map the identity cone on the target back to
the cone of an isomorphism. -/
theorem identityConeToMappingConeIso_comm
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    𝟙 target ≫ 𝟙 target = inv hom ≫ hom :=
  Eq.trans
    (Category.id_comp (𝟙 target))
    (Eq.symm (IsIso.inv_hom_id hom))

/-- The concrete map from the mapping cone of an isomorphism to the mapping
cone of the identity on its target. -/
def mappingConeIsoToIdentityConeMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone hom ⟶
      CochainComplex.mappingCone (𝟙 target) :=
  CochainComplex.mappingCone.map
    hom
    (𝟙 target)
    hom
    (𝟙 target)
    (TraceAnalyticAdditiveHomotopyCategory
      .mappingConeIsoToIdentityCone_comm hom)

/-- The concrete map from the identity cone on the target back to the mapping
cone of an isomorphism. -/
def identityConeToMappingConeIsoMap
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target)
    [IsIso hom] :
    CochainComplex.mappingCone (𝟙 target) ⟶
      CochainComplex.mappingCone hom :=
  CochainComplex.mappingCone.map
    (𝟙 target)
    hom
    (inv hom)
    (𝟙 target)
    (TraceAnalyticAdditiveHomotopyCategory
      .identityConeToMappingConeIso_comm hom)

end TraceAnalyticAdditiveHomotopyCategory

end AnalyticMotives
end LFunctions
end Boundary
