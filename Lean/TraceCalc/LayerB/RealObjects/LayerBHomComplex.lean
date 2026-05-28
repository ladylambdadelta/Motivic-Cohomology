import TraceCalc.LayerC.RealObjects.LayerBHomComplex

/-! Compatibility shim: the implementation moved to LayerC because it is a
derived homological layer built on LayerB foundations. -/import TraceCalc.LayerB.RealObjects.Composition
import TraceCalc.LayerA.CategoryInfra.H0Category

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

variable (setup : RewriteCalculusSetup.{u})

/-- Exact missing differential package on the first honest trace-side carrier.

The existing Layer B development already exposes:
- objects: `setup.State`
- raw trace-like morphisms: `setup.CertifiedTrace X Y`
- quotient morphisms: `setup.TraceClass X Y`
- quotient identity/composition: `TraceClass.id`, `TraceClass.compose`
- quotient map from raw to quotient: `CertifiedTrace.cls`

What it still does not expose is the dg-style differential layer needed to
declare cycles and boundaries on those raw morphisms. This structure records
exactly that missing data, without pretending it is already present in the
current trace formalization. -/
structure LayerBTraceDifferentialPackage (setup : RewriteCalculusSetup.{u}) where
  differentialRel :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → setup.CertifiedTrace X Y → Prop
  cycles :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → Prop
  boundaries :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → Prop
  zeroClass : ∀ {X Y : setup.State}, setup.TraceClass X Y
  quotientMapKillsBoundaries :
    ∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
      boundaries trace → trace.cls = zeroClass

namespace LayerBTraceDifferentialPackage

/-- First honest `LayerBHomComplexData` carrier built from existing Layer B
trace data.

This is concrete on the carrier side:
- objects are states;
- raw morphisms are certified traces;
- quotient morphisms are trace classes;
- quotient map is the `cls` projection.

It remains parameterized by the missing differential package because the current
workspace still has no non-fake notion of differential, cycle, or boundary on
certified traces. -/
def toLayerBHomComplexData (pkg : LayerBTraceDifferentialPackage setup) :
    CategoryInfra.LayerBHomComplexData.{u, u} where
  objects := setup.State
  morphismData X Y := setup.CertifiedTrace X Y
  quotientHom X Y := setup.TraceClass X Y
  id := TraceClass.id
  zero X Y := pkg.zeroClass
  comp := by
    intro X Y Z left right
    exact left.compose right
  differentialRel := by
    intro X Y left right
    exact pkg.differentialRel left right
  cycles := by
    intro X Y trace
    exact pkg.cycles trace
  boundaries := by
    intro X Y trace
    exact pkg.boundaries trace
  quotientMap := by
    intro X Y trace
    exact trace.cls
  quotientMapKillsBoundaries := pkg.quotientMapKillsBoundaries

@[simp] theorem toLayerBHomComplexData_objects
    (pkg : LayerBTraceDifferentialPackage setup) :
    (LayerBTraceDifferentialPackage.toLayerBHomComplexData (setup := setup) pkg).objects
      = setup.State :=
  rfl

@[simp] theorem toLayerBHomComplexData_morphismData
    (pkg : LayerBTraceDifferentialPackage setup)
    (X Y : setup.State) :
    (LayerBTraceDifferentialPackage.toLayerBHomComplexData (setup := setup) pkg).morphismData X Y
      = setup.CertifiedTrace X Y :=
  rfl

@[simp] theorem toLayerBHomComplexData_quotientHom
    (pkg : LayerBTraceDifferentialPackage setup)
    (X Y : setup.State) :
    (LayerBTraceDifferentialPackage.toLayerBHomComplexData (setup := setup) pkg).quotientHom X Y
      = setup.TraceClass X Y :=
  rfl

@[simp] theorem toLayerBHomComplexData_quotientMap
    (pkg : LayerBTraceDifferentialPackage setup)
    {X Y : setup.State} (trace : setup.CertifiedTrace X Y) :
    (LayerBTraceDifferentialPackage.toLayerBHomComplexData (setup := setup) pkg).quotientMap trace
      = trace.cls :=
  rfl

@[simp] theorem toLayerBHomComplexData_id
    (pkg : LayerBTraceDifferentialPackage setup)
    (X : setup.State) :
    (LayerBTraceDifferentialPackage.toLayerBHomComplexData (setup := setup) pkg).id X
      = TraceClass.id X :=
  rfl

@[simp] theorem toLayerBHomComplexData_comp
    (pkg : LayerBTraceDifferentialPackage setup)
    {X Y Z : setup.State}
    (left : setup.TraceClass X Y) (right : setup.TraceClass Y Z) :
    (LayerBTraceDifferentialPackage.toLayerBHomComplexData (setup := setup) pkg).comp left right
      = left.compose right :=
  rfl

end LayerBTraceDifferentialPackage

end RewriteCalculusSetup
end RealObjects
end LayerB
end TraceCalc