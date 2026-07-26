import Mathlib.Algebra.Homology.ShortComplex.QuasiIso

/-!
# Boundary short-complex models

This file owns the generic homological algebra for boundary replacements of a
short complex by its cycles or opcycles model.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The right-boundary model of a short complex.  It replaces the incoming
object by a zero incoming map and keeps the outgoing map induced from the
opcycles cokernel. -/
def rightBoundaryModel
    {C : Type*}
    [Category C]
    [HasZeroMorphisms C]
    (leftObject : C)
    (shortComplex : ShortComplex C)
    (rightData : shortComplex.RightHomologyData) :
    ShortComplex C :=
  ShortComplex.mk
    (0 : leftObject ⟶ rightData.Q)
    rightData.g'
    zero_comp

/-- The canonical map from a short complex to its right-boundary model. -/
def rightBoundaryProjection
    {C : Type*}
    [Category C]
    [HasZeroMorphisms C]
    {leftObject : C}
    (shortComplex : ShortComplex C)
    (rightData : shortComplex.RightHomologyData)
    (leftMap : shortComplex.X₁ ⟶ leftObject) :
    shortComplex ⟶
      TraceAnalyticDerivedMotiveCategory
        .rightBoundaryModel leftObject shortComplex rightData where
  τ₁ := leftMap
  τ₂ := rightData.p
  τ₃ := 𝟙 shortComplex.X₃
  comm₁₂ :=
    Eq.trans
      (Category.comp_zero leftMap)
      (Eq.symm rightData.wp)
  comm₂₃ :=
    Eq.trans
      rightData.p_g'
      (Eq.symm (Category.comp_id shortComplex.g))

/-- The right-boundary projection is a quasi-isomorphism: both homology
objects are the same kernel of the outgoing map from opcycles. -/
theorem rightBoundaryProjection_quasiIso
    {C : Type*}
    [Category C]
    [HasZeroMorphisms C]
    (leftObject : C)
    (shortComplex : ShortComplex C)
    [shortComplex.HasHomology]
    (leftMap : shortComplex.X₁ ⟶ leftObject) :
    ShortComplex.QuasiIso
      (TraceAnalyticDerivedMotiveCategory
        .rightBoundaryProjection
          (leftObject := leftObject)
          shortComplex
          shortComplex.homologyData.right
          leftMap) :=
  let rightData : shortComplex.RightHomologyData :=
    shortComplex.homologyData.right
  let boundaryModel : ShortComplex C :=
    TraceAnalyticDerivedMotiveCategory
      .rightBoundaryModel leftObject shortComplex rightData
  let boundaryKernel : KernelFork boundaryModel.g :=
    KernelFork.ofι rightData.ι rightData.ι_g'
  let boundaryHomologyData : boundaryModel.HomologyData :=
    ShortComplex.HomologyData.ofIsLimitKernelFork
      boundaryModel
      rfl
      boundaryKernel
      rightData.hι'
  let projection :
      shortComplex ⟶ boundaryModel :=
    TraceAnalyticDerivedMotiveCategory
      .rightBoundaryProjection shortComplex rightData leftMap
  let projectionRightData :
      ShortComplex.RightHomologyMapData
        projection
        rightData
        boundaryHomologyData.right :=
    { φQ := 𝟙 rightData.Q
      φH := 𝟙 rightData.H
      commp :=
        Eq.trans
          (Category.comp_id rightData.p)
          (Eq.symm (Category.comp_id rightData.p))
      commg' :=
        Eq.trans
          (Category.id_comp boundaryHomologyData.right.g')
          (Eq.trans
            (congrArg
              (fun morphism : rightData.Q ⟶ shortComplex.X₃ => morphism)
              (ShortComplex.RightHomologyData.ofIsLimitKernelFork_g'
                boundaryModel
                rfl
                boundaryKernel
                rightData.hι'))
            (Eq.symm (Category.comp_id rightData.g')))
      commι :=
        Eq.trans
          (Category.id_comp boundaryHomologyData.right.ι)
          (Eq.symm (Category.comp_id rightData.ι)) }
  (ShortComplex.RightHomologyMapData.quasiIso_iff
    projectionRightData).mpr
    inferInstance

/-- The left-boundary model of a short complex.  It replaces the outgoing
object by a zero outgoing map and keeps the incoming map induced into the
cycles kernel. -/
def leftBoundaryModel
    {C : Type*}
    [Category C]
    [HasZeroMorphisms C]
    (shortComplex : ShortComplex C)
    (leftData : shortComplex.LeftHomologyData)
    (rightObject : C) :
    ShortComplex C :=
  ShortComplex.mk
    leftData.f'
    (0 : leftData.K ⟶ rightObject)
    comp_zero

/-- The canonical map from the left-boundary model into the original short
complex. -/
def leftBoundaryInclusion
    {C : Type*}
    [Category C]
    [HasZeroMorphisms C]
    (shortComplex : ShortComplex C)
    (leftData : shortComplex.LeftHomologyData)
    {rightObject : C}
    (rightMap : rightObject ⟶ shortComplex.X₃) :
    TraceAnalyticDerivedMotiveCategory
        .leftBoundaryModel shortComplex leftData rightObject ⟶
      shortComplex where
  τ₁ := 𝟙 shortComplex.X₁
  τ₂ := leftData.i
  τ₃ := rightMap
  comm₁₂ :=
    Eq.trans
      (Category.id_comp shortComplex.f)
      (Eq.symm leftData.f'_i)
  comm₂₃ :=
    Eq.trans
      (Category.zero_comp rightMap)
      (Eq.symm leftData.wi)

/-- The left-boundary inclusion is a quasi-isomorphism: both homology objects
are the same cokernel of the incoming map into cycles. -/
theorem leftBoundaryInclusion_quasiIso
    {C : Type*}
    [Category C]
    [HasZeroMorphisms C]
    (shortComplex : ShortComplex C)
    [shortComplex.HasHomology]
    (rightObject : C)
    (rightMap : rightObject ⟶ shortComplex.X₃) :
    ShortComplex.QuasiIso
      (TraceAnalyticDerivedMotiveCategory
        .leftBoundaryInclusion
          shortComplex
          shortComplex.homologyData.left
          rightMap) :=
  let leftData : shortComplex.LeftHomologyData :=
    shortComplex.homologyData.left
  let boundaryModel : ShortComplex C :=
    TraceAnalyticDerivedMotiveCategory
      .leftBoundaryModel shortComplex leftData rightObject
  let boundaryCokernel : CokernelCofork boundaryModel.f :=
    CokernelCofork.ofπ leftData.π leftData.f'_π
  let boundaryHomologyData : boundaryModel.HomologyData :=
    ShortComplex.HomologyData.ofIsColimitCokernelCofork
      boundaryModel
      rfl
      boundaryCokernel
      leftData.hπ'
  let inclusion :
      boundaryModel ⟶ shortComplex :=
    TraceAnalyticDerivedMotiveCategory
      .leftBoundaryInclusion shortComplex leftData rightMap
  let inclusionLeftData :
      ShortComplex.LeftHomologyMapData
        inclusion
        boundaryHomologyData.left
        leftData :=
    { φK := 𝟙 leftData.K
      φH := 𝟙 leftData.H
      commi :=
        Eq.trans
          (Category.id_comp leftData.i)
          (Eq.symm (Category.comp_id leftData.i))
      commf' :=
        Eq.trans
          (congrArg
            (fun morphism : shortComplex.X₁ ⟶ leftData.K => morphism)
            (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork_f'
              boundaryModel
              rfl
              boundaryCokernel
              leftData.hπ'))
          (Eq.symm (Category.id_comp leftData.f'))
      commπ :=
        Eq.trans
          (Category.comp_id boundaryHomologyData.left.π)
          (Eq.symm (Category.id_comp leftData.π)) }
  (ShortComplex.LeftHomologyMapData.quasiIso_iff
    inclusionLeftData).mpr
    inferInstance

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
