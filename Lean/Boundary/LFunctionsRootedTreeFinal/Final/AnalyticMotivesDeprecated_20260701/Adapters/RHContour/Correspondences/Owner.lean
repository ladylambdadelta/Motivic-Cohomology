import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Owner

/-!
# RH contour relation adapter

This file owns the RH-specific relation model: relations between imported RH
singular supports at contour heights.  It is useful for trace-realization
tests, but it is not the generic analytic correspondence category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- RH-specific relation correspondences between adapter objects. -/
abbrev RHContourAdapterCorrespondence
    (X Y : RHContourAdapterObject) :=
  RHContourRelationCorrespondence X Y

/--
Identity RH contour relation: the same singular support point at the same
height on the same RH contour adapter object.
-/
def RHContourRelationCorrespondence.id
    (X : RHContourAdapterObject) :
    RHContourAdapterCorrespondence X X where
  relation TX TY :=
    {p : ℂ × ℂ |
      TX = TY ∧ p.1 = p.2 ∧
        p.1 ∈ X.singularSupportAt TX ∧
          p.2 ∈ X.singularSupportAt TY}
  source_mem TX TY p hp :=
    hp.2.2.1
  target_mem TX TY p hp :=
    hp.2.2.2

/--
Composition of RH contour relations by existential composition of singular
supports at an intermediate height.
-/
def RHContourRelationCorrespondence.comp
    {X Y Z : RHContourAdapterObject}
    (F : RHContourAdapterCorrespondence X Y)
    (G : RHContourAdapterCorrespondence Y Z) :
    RHContourAdapterCorrespondence X Z where
  relation TX TZ :=
    {p : ℂ × ℂ |
      ∃ TY : Y.Stage,
        ∃ y : ℂ,
          (p.1, y) ∈ F.relation TX TY ∧
            (y, p.2) ∈ G.relation TY TZ}
  source_mem TX TZ p hp :=
    match hp with
    | ⟨TY, y, hF, _hG⟩ =>
        F.mem_source TX TY (p.1, y) hF
  target_mem TX TZ p hp :=
    match hp with
    | ⟨TY, y, _hF, hG⟩ =>
        G.mem_target TY TZ (y, p.2) hG

namespace RHContourAdapterCorrespondence

/-- The identity RH adapter correspondence. -/
def identity (X : RHContourAdapterObject) :
    RHContourAdapterCorrespondence X X :=
  RHContourRelationCorrespondence.id X

/-- Composition of RH adapter correspondences by relation composition. -/
def comp {X Y Z : RHContourAdapterObject}
    (F : RHContourAdapterCorrespondence X Y)
    (G : RHContourAdapterCorrespondence Y Z) :
    RHContourAdapterCorrespondence X Z :=
  RHContourRelationCorrespondence.comp F G

/-- Source support membership for an RH adapter correspondence. -/
theorem mem_source {X Y : RHContourAdapterObject}
    (F : RHContourAdapterCorrespondence X Y)
    (TX : X.Stage) (TY : Y.Stage) (p : ℂ × ℂ)
    (hp : p ∈ F.relation TX TY) :
    p.1 ∈ X.singularSupportAt TX :=
  F.mem_source TX TY p hp

/-- Target support membership for an RH adapter correspondence. -/
theorem mem_target {X Y : RHContourAdapterObject}
    (F : RHContourAdapterCorrespondence X Y)
    (TX : X.Stage) (TY : Y.Stage) (p : ℂ × ℂ)
    (hp : p ∈ F.relation TX TY) :
    p.2 ∈ Y.singularSupportAt TY :=
  F.mem_target TX TY p hp

/-- Membership in a composed RH adapter correspondence has source support. -/
theorem comp_mem_source
    {X Y Z : RHContourAdapterObject}
    (F : RHContourAdapterCorrespondence X Y)
    (G : RHContourAdapterCorrespondence Y Z)
    (TX : X.Stage) (TZ : Z.Stage) (p : ℂ × ℂ)
    (hp : p ∈ (comp F G).relation TX TZ) :
    p.1 ∈ X.singularSupportAt TX :=
  (comp F G).mem_source TX TZ p hp

/-- Membership in a composed RH adapter correspondence has target support. -/
theorem comp_mem_target
    {X Y Z : RHContourAdapterObject}
    (F : RHContourAdapterCorrespondence X Y)
    (G : RHContourAdapterCorrespondence Y Z)
    (TX : X.Stage) (TZ : Z.Stage) (p : ℂ × ℂ)
    (hp : p ∈ (comp F G).relation TX TZ) :
    p.2 ∈ Z.singularSupportAt TZ :=
  (comp F G).mem_target TX TZ p hp

end RHContourAdapterCorrespondence

end AnalyticMotives
end LFunctions
end Boundary
