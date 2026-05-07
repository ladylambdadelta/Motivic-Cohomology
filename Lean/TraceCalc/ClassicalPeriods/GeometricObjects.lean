import TraceCalc.ClassicalPeriods.Basic

universe u v w x y

namespace TraceCalc
namespace ClassicalPeriods

/-- Lightweight geometric source object for the classical period lane.

This is only the typed host for later geometric constructions. It does not yet claim an actual
scheme, variety, or motivic model. -/
structure GeometricPeriodObject
    (ctx : ClassicalComparisonContext.{u, v}) where
  Carrier : Type w
  object : Carrier
  geometricAdmissibilityTarget : Prop
  realizationDefinedTarget : Prop

namespace GeometricPeriodObject

/-- Helper constructor for the lightweight geometric source-object interface. -/
def ofObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (Carrier : Type w)
    (object : Carrier)
    (geometricAdmissibilityTarget realizationDefinedTarget : Prop) :
    GeometricPeriodObject ctx where
  Carrier := Carrier
  object := object
  geometricAdmissibilityTarget := geometricAdmissibilityTarget
  realizationDefinedTarget := realizationDefinedTarget

@[simp] theorem ofObject_carrier
    {ctx : ClassicalComparisonContext.{u, v}}
    (Carrier : Type w)
    (object : Carrier)
    (geometricAdmissibilityTarget realizationDefinedTarget : Prop) :
    (GeometricPeriodObject.ofObject (ctx := ctx)
      Carrier object geometricAdmissibilityTarget realizationDefinedTarget).Carrier = Carrier := rfl

@[simp] theorem ofObject_object
    {ctx : ClassicalComparisonContext.{u, v}}
    (Carrier : Type w)
    (object : Carrier)
    (geometricAdmissibilityTarget realizationDefinedTarget : Prop) :
    (GeometricPeriodObject.ofObject (ctx := ctx)
      Carrier object geometricAdmissibilityTarget realizationDefinedTarget).object = object := rfl

@[simp] theorem ofObject_geometricAdmissibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (Carrier : Type w)
    (object : Carrier)
    (geometricAdmissibilityTarget realizationDefinedTarget : Prop) :
    (GeometricPeriodObject.ofObject (ctx := ctx)
      Carrier object geometricAdmissibilityTarget realizationDefinedTarget).geometricAdmissibilityTarget =
      geometricAdmissibilityTarget := rfl

@[simp] theorem ofObject_realizationDefinedTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (Carrier : Type w)
    (object : Carrier)
    (geometricAdmissibilityTarget realizationDefinedTarget : Prop) :
    (GeometricPeriodObject.ofObject (ctx := ctx)
      Carrier object geometricAdmissibilityTarget realizationDefinedTarget).realizationDefinedTarget =
      realizationDefinedTarget := rfl

end GeometricPeriodObject

/-- Lightweight correspondence between two geometric source objects. -/
structure GeometricCorrespondence
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : GeometricPeriodObject ctx) where
  correspondenceTarget : Prop
  compositionTarget : Prop
  identityTarget : Prop

namespace GeometricCorrespondence

/-- Helper constructor for the lightweight correspondence interface. -/
def ofTargets
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : GeometricPeriodObject ctx}
    (correspondenceTarget compositionTarget identityTarget : Prop) :
    GeometricCorrespondence source target where
  correspondenceTarget := correspondenceTarget
  compositionTarget := compositionTarget
  identityTarget := identityTarget

@[simp] theorem ofTargets_correspondenceTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : GeometricPeriodObject ctx}
    (correspondenceTarget compositionTarget identityTarget : Prop) :
  (GeometricCorrespondence.ofTargets (source := source) (target := target)
      correspondenceTarget compositionTarget identityTarget).correspondenceTarget = correspondenceTarget := rfl

@[simp] theorem ofTargets_compositionTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : GeometricPeriodObject ctx}
    (correspondenceTarget compositionTarget identityTarget : Prop) :
  (GeometricCorrespondence.ofTargets (source := source) (target := target)
      correspondenceTarget compositionTarget identityTarget).compositionTarget = compositionTarget := rfl

@[simp] theorem ofTargets_identityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : GeometricPeriodObject ctx}
    (correspondenceTarget compositionTarget identityTarget : Prop) :
  (GeometricCorrespondence.ofTargets (source := source) (target := target)
      correspondenceTarget compositionTarget identityTarget).identityTarget = identityTarget := rfl

end GeometricCorrespondence

/-- Framed geometric object carrying the source-side data from which framed periods will later be
extracted. -/
structure GeometricFramedObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (object : GeometricPeriodObject ctx) where
  FrameCarrier : Type x
  CycleCarrier : Type y
  frame : FrameCarrier
  cycle : CycleCarrier
  framingAdmissibilityTarget : Prop
  framingFunctorialityTarget : Prop

namespace GeometricFramedObject

/-- Helper constructor for framed geometric source data. -/
def ofFrameAndCycle
    {ctx : ClassicalComparisonContext.{u, v}}
    {object : GeometricPeriodObject ctx}
    (FrameCarrier : Type x)
    (CycleCarrier : Type y)
    (frame : FrameCarrier)
    (cycle : CycleCarrier)
    (framingAdmissibilityTarget framingFunctorialityTarget : Prop) :
    GeometricFramedObject object where
  FrameCarrier := FrameCarrier
  CycleCarrier := CycleCarrier
  frame := frame
  cycle := cycle
  framingAdmissibilityTarget := framingAdmissibilityTarget
  framingFunctorialityTarget := framingFunctorialityTarget

@[simp] theorem ofFrameAndCycle_frame
    {ctx : ClassicalComparisonContext.{u, v}}
    {object : GeometricPeriodObject ctx}
    (FrameCarrier : Type x)
    (CycleCarrier : Type y)
    (frame : FrameCarrier)
    (cycle : CycleCarrier)
    (framingAdmissibilityTarget framingFunctorialityTarget : Prop) :
    (GeometricFramedObject.ofFrameAndCycle (object := object) FrameCarrier CycleCarrier frame cycle
      framingAdmissibilityTarget framingFunctorialityTarget).frame = frame := rfl

@[simp] theorem ofFrameAndCycle_cycle
    {ctx : ClassicalComparisonContext.{u, v}}
    {object : GeometricPeriodObject ctx}
    (FrameCarrier : Type x)
    (CycleCarrier : Type y)
    (frame : FrameCarrier)
    (cycle : CycleCarrier)
    (framingAdmissibilityTarget framingFunctorialityTarget : Prop) :
    (GeometricFramedObject.ofFrameAndCycle (object := object) FrameCarrier CycleCarrier frame cycle
      framingAdmissibilityTarget framingFunctorialityTarget).cycle = cycle := rfl

@[simp] theorem ofFrameAndCycle_framingAdmissibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {object : GeometricPeriodObject ctx}
    (FrameCarrier : Type x)
    (CycleCarrier : Type y)
    (frame : FrameCarrier)
    (cycle : CycleCarrier)
    (framingAdmissibilityTarget framingFunctorialityTarget : Prop) :
    (GeometricFramedObject.ofFrameAndCycle (object := object) FrameCarrier CycleCarrier frame cycle
      framingAdmissibilityTarget framingFunctorialityTarget).framingAdmissibilityTarget =
        framingAdmissibilityTarget := rfl

@[simp] theorem ofFrameAndCycle_framingFunctorialityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {object : GeometricPeriodObject ctx}
    (FrameCarrier : Type x)
    (CycleCarrier : Type y)
    (frame : FrameCarrier)
    (cycle : CycleCarrier)
    (framingAdmissibilityTarget framingFunctorialityTarget : Prop) :
    (GeometricFramedObject.ofFrameAndCycle (object := object) FrameCarrier CycleCarrier frame cycle
      framingAdmissibilityTarget framingFunctorialityTarget).framingFunctorialityTarget =
        framingFunctorialityTarget := rfl

end GeometricFramedObject

end ClassicalPeriods
end TraceCalc