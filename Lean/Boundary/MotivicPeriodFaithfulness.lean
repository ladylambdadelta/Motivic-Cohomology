import Boundary.GeometricRecognition
import Boundary.Scaffold

open CategoryTheory

/-!
# Motivic Period Faithfulness Bridge

This file contains only the direct formal theorem closing the boundary-side
scaffold once a recognized geometric-motive target has been equipped with a
concrete probe family and a concrete period invariant.

It intentionally exports no extra wrapper/package records.
-/

universe u v w x

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary

noncomputable section

namespace BoundaryMotivicProgramQ

/-- Direct formal closeout on top of a recognized motivic target.

This theorem is the only content exported from this file: once a concrete probe
family and concrete period invariant on the recognized target category are in
hand, tomography plus holography imply period faithfulness. -/
theorem periodFaithfulness_of_holography_of_tomography
    {category : SmCorQ (k := k)}
    (program : BoundaryMotivicProgramQ category)
    [Category.{v} program.recognition.DMgmQObj]
    (probeFamily : ProbeFamily program.recognition.DMgmQObj)
    (periodInvariant :
      ∀ {X Y : program.recognition.DMgmQObj}, (X ⟶ Y) → Type w)
    (hHolo : Holography probeFamily)
    (hTomo : Tomography probeFamily periodInvariant) :
    PeriodFaithfulness periodInvariant :=
  tomography_implies_periodFaithfulness probeFamily periodInvariant hHolo hTomo

end BoundaryMotivicProgramQ

end

end Boundary
