import TraceCalc.ProbeTheory.BoundaryData
import TraceCalc.ProbeTheory.Separating

universe u v w x y z

namespace TraceCalc
namespace ProbeTheory

/-- A morphism reconstructed from coherent probe-boundary data. -/
structure ProbeMorphismReconstructionData
    (C : CategoryLike.{u, v})
    (P : ProbeFamily.{u, v, w} C)
    (Obs : ProbeObservation.{u, v, w, x} C P) where
  reconstructHom : {X Y : C.Obj} ->
    CoherentProbeBoundaryData.{u, v, w, y} C P X ->
    CoherentProbeBoundaryData.{u, v, w, y} C P Y ->
    C.Hom X Y
  BoundaryMapCompatibility : {X Y : C.Obj} ->
    CoherentProbeBoundaryData.{u, v, w, y} C P X ->
    CoherentProbeBoundaryData.{u, v, w, y} C P Y -> C.Hom X Y -> Prop
  compatibility : {X Y : C.Obj} ->
    (source : CoherentProbeBoundaryData.{u, v, w, y} C P X) ->
    (target : CoherentProbeBoundaryData.{u, v, w, y} C P Y) ->
      BoundaryMapCompatibility source target (reconstructHom source target)

/-- If reconstructed morphisms have the same observations, separating probes
identify them. -/
theorem reconstructed_morphisms_eq_of_probe_agreement
    {C : CategoryLike.{u, v}}
    {P : ProbeFamily.{u, v, w} C}
    {Obs : ProbeObservation.{u, v, w, x} C P}
    (Sep : SeparatingProbeFamily C P Obs)
    {X Y : C.Obj}
    {f g : C.Hom X Y}
    (h : Obs.MapAgreement f g) :
    f = g :=
  separating_probes_detect_morphisms Sep h

/-- Object reconstruction correctness projected under its own named interface. -/
theorem probe_reconstruction_correct
    {C : CategoryLike.{u, v}}
    {P : ProbeFamily.{u, v, w} C}
    {X : C.Obj}
    (R : ProbeReconstructionData C P X)
    (boundary : CoherentProbeBoundaryData.{u, v, w, y} C P X) :
    R.ReconstructionRelation boundary (R.reconstruct boundary) :=
  R.correctness boundary

/-- Morphism reconstruction correctness projected under its own named interface. -/
theorem probe_morphism_reconstruction_correct
    {C : CategoryLike.{u, v}}
    {P : ProbeFamily.{u, v, w} C}
    {Obs : ProbeObservation.{u, v, w, x} C P}
    (R : ProbeMorphismReconstructionData C P Obs)
    {X Y : C.Obj}
    (source : CoherentProbeBoundaryData.{u, v, w, y} C P X)
    (target : CoherentProbeBoundaryData.{u, v, w, y} C P Y) :
    R.BoundaryMapCompatibility source target (R.reconstructHom source target) :=
  R.compatibility source target

end ProbeTheory
end TraceCalc
