import TraceCalc.LayerC.ProbeTheory.Separating

universe u v w x y

namespace TraceCalc
namespace ProbeTheory

/-- Boundary maps from each probe object into a target object. -/
structure ProbeBoundaryData
    (C : CategoryLike.{u, v})
    (P : ProbeFamily.{u, v, w} C)
    (X : C.Obj) where
  boundary : (i : P.ProbeIndex) -> C.Hom (P.probe i) X

/-- A proof-relevant coherence specification for probe boundaries.  The relation is
supplied by the geometric or categorical application and is carried as data. -/
structure ProbeBoundaryCoherence
    (C : CategoryLike.{u, v})
    (P : ProbeFamily.{u, v, w} C)
    (X : C.Obj)
    (data : ProbeBoundaryData C P X) where
  BoundaryRelation : (i j : P.ProbeIndex) ->
    C.Hom (P.probe i) X -> C.Hom (P.probe j) X -> Type y
  coherent : (i j : P.ProbeIndex) ->
    BoundaryRelation i j (data.boundary i) (data.boundary j)

/-- Boundary data together with proof-relevant compatibility between probe faces. -/
structure CoherentProbeBoundaryData
    (C : CategoryLike.{u, v})
    (P : ProbeFamily.{u, v, w} C)
    (X : C.Obj) where
  data : ProbeBoundaryData C P X
  coherence : ProbeBoundaryCoherence.{u, v, w, y} C P X data

/-- Reconstruction interface from coherent probe boundary data.  Correctness is an
application-specific relation, not erased to a vacuous proposition. -/
structure ProbeReconstructionData
    (C : CategoryLike.{u, v})
    (P : ProbeFamily.{u, v, w} C)
    (X : C.Obj) where
  reconstruct : CoherentProbeBoundaryData.{u, v, w, y} C P X -> C.Obj
  ReconstructionRelation :
    CoherentProbeBoundaryData.{u, v, w, y} C P X -> C.Obj -> Prop
  correctness :
    (boundary : CoherentProbeBoundaryData.{u, v, w, y} C P X) ->
      ReconstructionRelation boundary (reconstruct boundary)

namespace ProbeReconstructionData

variable {C : CategoryLike.{u, v}}
variable {P : ProbeFamily.{u, v, w} C}
variable {X : C.Obj}
variable (R : ProbeReconstructionData C P X)

def reconstructedObject
    (boundary : CoherentProbeBoundaryData.{u, v, w, y} C P X) : C.Obj :=
  R.reconstruct boundary

theorem reconstructedObject_correct
    (boundary : CoherentProbeBoundaryData.{u, v, w, y} C P X) :
    R.ReconstructionRelation boundary (R.reconstructedObject boundary) := by
  cases R with
  | mk reconstruct ReconstructionRelation correctness => exact correctness boundary

end ProbeReconstructionData

end ProbeTheory
end TraceCalc
