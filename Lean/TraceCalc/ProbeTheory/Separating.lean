import TraceCalc.ProbeTheory.Basic

universe u v w x

namespace TraceCalc
namespace ProbeTheory

/-- Probe families whose observations separate parallel morphisms. -/
structure SeparatingProbeFamily
    (C : CategoryLike.{u, v})
    (P : ProbeFamily.{u, v, w} C)
    (Obs : ProbeObservation.{u, v, w, x} C P) where
  map_ext :
    {X Y : C.Obj} -> {f g : C.Hom X Y} ->
      Obs.MapAgreement f g -> f = g

variable {C : CategoryLike.{u, v}}
variable {P : ProbeFamily.{u, v, w} C}
variable {Obs : ProbeObservation.{u, v, w, x} C P}
/-- Pointwise agreement on every probe observation implies equality of morphisms. -/
theorem probe_extensionality (separating : SeparatingProbeFamily C P Obs)
  {X Y : C.Obj} {f g : C.Hom X Y}
    (h : forall i observation,
      Obs.observeMap f i observation = Obs.observeMap g i observation) :
    f = g := by
  cases separating with
  | mk map_ext => exact map_ext h

/-- A named copy of probe extensionality for downstream packages. -/
theorem separating_probes_detect_morphisms (separating : SeparatingProbeFamily C P Obs)
  {X Y : C.Obj} {f g : C.Hom X Y}
    (h : Obs.MapAgreement f g) :
    f = g := by
  cases separating with
  | mk map_ext => exact map_ext h

/-- Separating probes detect equality after composing with a fixed outgoing map,
provided the observed composites agree. -/
theorem separating_probes_detect_postcomposition (separating : SeparatingProbeFamily C P Obs)
  {X Y Z : C.Obj}
    {f g : C.Hom X Y} (k : C.Hom Y Z)
    (h : Obs.MapAgreement (C.comp f k) (C.comp g k)) :
    C.comp f k = C.comp g k := by
  cases separating with
  | mk map_ext => exact map_ext h

end ProbeTheory
end TraceCalc
