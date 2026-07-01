import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Transport.Composition.Owner

/-!
# Composition of contour-compatible correspondences

This owner is the categorical checkpoint for the morphism layer: identities,
composition, and associativity of contour-compatible analytic correspondences
belong here after support, transport, and residue compatibility have been
constructed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Composition data for contour-compatible analytic correspondences.  It records a
chosen composite correspondence together with the transport-composition and
residue-stability data that certify the composite respects the contour
calculus.
-/
structure ContourCorrespondenceCompositionData
    {X Y Z : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y)
    (G : ContourAnalyticCorrespondence Y Z) where
  composite : ContourAnalyticCorrespondence X Z
  transportComposition :
    AnalyticContourTransportCompositionData
      composite.support F.transport G.transport
  residueStability :
    AnalyticResidueCompositionStabilityData composite.transport

namespace ContourCorrespondenceCompositionData

/-- The composite contour-compatible correspondence selected by composition data. -/
def correspondence {X Y Z : ContourAdmissibleBulk}
    {F : ContourAnalyticCorrespondence X Y}
    {G : ContourAnalyticCorrespondence Y Z}
    (C : ContourCorrespondenceCompositionData F G) :
    ContourAnalyticCorrespondence X Z :=
  C.composite

/-- The transport-composition data carried by correspondence composition. -/
def transportData {X Y Z : ContourAdmissibleBulk}
    {F : ContourAnalyticCorrespondence X Y}
    {G : ContourAnalyticCorrespondence Y Z}
    (C : ContourCorrespondenceCompositionData F G) :
    AnalyticContourTransportCompositionData
      C.composite.support F.transport G.transport :=
  C.transportComposition

/-- The residue-stability data carried by correspondence composition. -/
def residueData {X Y Z : ContourAdmissibleBulk}
    {F : ContourAnalyticCorrespondence X Y}
    {G : ContourAnalyticCorrespondence Y Z}
    (C : ContourCorrespondenceCompositionData F G) :
    AnalyticResidueCompositionStabilityData C.composite.transport :=
  C.residueStability

end ContourCorrespondenceCompositionData

/--
Category-law data for the contour-correspondence calculus.  It records the
chosen identities, composition data, and the identity/associativity equations
for contour-compatible correspondences.

This is a compatibility surface for the earlier scaffold.  The intended owner
construction is below this layer: support composition by analytic fiber
product, transport composition, and residue-stability proofs should construct
identity, composition, and the category laws before downstream presheaves use
them.
-/
structure ContourCorrespondenceCategoryLawData where
  identity :
    (X : ContourAdmissibleBulk) →
      ContourCorrespondenceIdentityData X
  compose :
    {X Y Z : ContourAdmissibleBulk} →
      (F : ContourAnalyticCorrespondence X Y) →
        (G : ContourAnalyticCorrespondence Y Z) →
          ContourCorrespondenceCompositionData F G
  left_identity :
    {X Y : ContourAdmissibleBulk} →
      (F : ContourAnalyticCorrespondence X Y) →
        (compose (identity X).identity F).composite = F
  right_identity :
    {X Y : ContourAdmissibleBulk} →
      (F : ContourAnalyticCorrespondence X Y) →
        (compose F (identity Y).identity).composite = F
  associativity :
    {W X Y Z : ContourAdmissibleBulk} →
      (F : ContourAnalyticCorrespondence W X) →
        (G : ContourAnalyticCorrespondence X Y) →
          (H : ContourAnalyticCorrespondence Y Z) →
            (compose (compose F G).composite H).composite =
              (compose F (compose G H).composite).composite

namespace ContourCorrespondenceCategoryLawData

/-- The identity contour correspondence selected by category-law data. -/
def identityAt (C : ContourCorrespondenceCategoryLawData)
    (X : ContourAdmissibleBulk) :
    ContourAnalyticCorrespondence X X :=
  (C.identity X).identity

/-- The composite contour correspondence selected by category-law data. -/
def composeAt (C : ContourCorrespondenceCategoryLawData)
    {X Y Z : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y)
    (G : ContourAnalyticCorrespondence Y Z) :
    ContourAnalyticCorrespondence X Z :=
  (C.compose F G).composite

/-- Left identity law for selected contour-correspondence composition. -/
theorem left_identity_eq (C : ContourCorrespondenceCategoryLawData)
    {X Y : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y) :
    C.composeAt (C.identityAt X) F = F :=
  C.left_identity F

/-- Right identity law for selected contour-correspondence composition. -/
theorem right_identity_eq (C : ContourCorrespondenceCategoryLawData)
    {X Y : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y) :
    C.composeAt F (C.identityAt Y) = F :=
  C.right_identity F

/-- Associativity law for selected contour-correspondence composition. -/
theorem associativity_eq (C : ContourCorrespondenceCategoryLawData)
    {W X Y Z : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence W X)
    (G : ContourAnalyticCorrespondence X Y)
    (H : ContourAnalyticCorrespondence Y Z) :
    C.composeAt (C.composeAt F G) H =
      C.composeAt F (C.composeAt G H) :=
  C.associativity F G H

end ContourCorrespondenceCategoryLawData

end AnalyticMotives
end LFunctions
end Boundary
