import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Owner
import Mathlib.CategoryTheory.Category.Basic

/-!
# Category of contour-compatible correspondences

This file owns the category-level packaging of contour-compatible analytic
correspondences after identity and composition laws have been established in
the correspondence layer.

Foundational source: mathlib's category API supplies the categorical structure
used by the transfer-presheaf layer.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The object type of the contour-correspondence graph. -/
abbrev ContourCorrespondenceObject : Type :=
  ContourAdmissibleBulk

/--
The morphism type of the contour-correspondence graph.  A later owner theorem
promotes this graph to a category after identity and associativity data have
been constructed at the correspondence-composition layer.
-/
abbrev ContourCorrespondenceHom
    (X Y : ContourCorrespondenceObject) : Type :=
  ContourAnalyticCorrespondence X Y

/--
The graph underlying contour-compatible correspondences.  This is the input for
formal rational linearization before the category laws are installed.
-/
structure ContourCorrespondenceGraph where
  Obj : Type
  Hom : Obj → Obj → Type

namespace ContourCorrespondenceGraph

/-- The graph whose objects are contour-admissible bulks and whose arrows are contour correspondences. -/
def analytic : ContourCorrespondenceGraph where
  Obj := ContourCorrespondenceObject
  Hom := ContourCorrespondenceHom

end ContourCorrespondenceGraph

/--
Category-level data for contour-compatible correspondences, exposed to the
transfer layer without installing a Lean `Category` instance at this stage.
-/
structure ContourCorrespondenceCategoryData where
  graph : ContourCorrespondenceGraph
  laws : ContourCorrespondenceCategoryLawData

namespace ContourCorrespondenceCategoryData

/-- The analytic contour-correspondence category data over the standard graph. -/
def analytic (laws : ContourCorrespondenceCategoryLawData) :
    ContourCorrespondenceCategoryData where
  graph := ContourCorrespondenceGraph.analytic
  laws := laws

end ContourCorrespondenceCategoryData

end AnalyticMotives
end LFunctions
end Boundary
