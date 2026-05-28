universe u v w x

namespace TraceCalc
namespace ProbeTheory

/-- Minimal category-shaped interface for the probe package.  The package uses only
identity and composition together with the laws carried by observations. -/
structure CategoryLike where
  Obj : Type u
  Hom : Obj -> Obj -> Type v
  id : (X : Obj) -> Hom X X
  comp : {X Y Z : Obj} -> Hom X Y -> Hom Y Z -> Hom X Z

namespace CategoryLike

variable (C : CategoryLike.{u, v})

def endomorphism (X : C.Obj) : Type v :=
  C.Hom X X

end CategoryLike

/-- A family of test objects.  The index type is part of the data, so probes are
not collapsed to a terminal probe family. -/
structure ProbeFamily (C : CategoryLike.{u, v}) where
  ProbeIndex : Type w
  probe : ProbeIndex -> C.Obj

/-- Functorial observations of objects through a probe family. -/
structure ProbeObservation
    (C : CategoryLike.{u, v})
    (P : ProbeFamily.{u, v, w} C) where
  observeObj : C.Obj -> P.ProbeIndex -> Type x
  observeMap :
    {X Y : C.Obj} -> C.Hom X Y -> (i : P.ProbeIndex) ->
      observeObj X i -> observeObj Y i
  observe_id :
    {X : C.Obj} -> (i : P.ProbeIndex) ->
      observeMap (C.id X) i = id
  observe_comp :
    {X Y Z : C.Obj} -> (f : C.Hom X Y) -> (g : C.Hom Y Z) ->
      (i : P.ProbeIndex) ->
        observeMap (C.comp f g) i = observeMap g i ∘ observeMap f i

namespace ProbeObservation

variable {C : CategoryLike.{u, v}}
variable {P : ProbeFamily.{u, v, w} C}
variable (Obs : ProbeObservation.{u, v, w, x} C P)

/-- Pointwise equality of observed morphisms. -/
def MapAgreement {X Y : C.Obj} (f g : C.Hom X Y) : Prop :=
  forall i observation, Obs.observeMap f i observation = Obs.observeMap g i observation

theorem mapAgreement_refl {X Y : C.Obj} (f : C.Hom X Y) :
    Obs.MapAgreement f f := by
  intro i observation
  rfl

theorem observed_id_apply {X : C.Obj} (i : P.ProbeIndex)
    (observation : Obs.observeObj X i) :
    Obs.observeMap (C.id X) i observation = observation := by
  have h := Obs.observe_id (X := X) i
  exact congrFun h observation

theorem observed_comp_apply {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z)
    (i : P.ProbeIndex) (observation : Obs.observeObj X i) :
    Obs.observeMap (C.comp f g) i observation =
      Obs.observeMap g i (Obs.observeMap f i observation) := by
  have h := Obs.observe_comp f g i
  exact congrFun h observation

end ProbeObservation

end ProbeTheory
end TraceCalc
