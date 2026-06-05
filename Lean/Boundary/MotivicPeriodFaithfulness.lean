import Boundary.Scaffold

open CategoryTheory

/-!
# Motivic Period Faithfulness Bridge

This file contains only the direct formal theorem closing the boundary-side
scaffold once a concrete target category has been equipped with a probe family
and a concrete period invariant.

It intentionally exports no extra wrapper/package records.
-/

universe u v w x

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary

noncomputable section

/-- Direct formal closeout for any concrete target category.

This theorem is the only content exported from this file: once a concrete probe
family and concrete period invariant on the target category are in
hand, tomography plus holography imply period faithfulness. -/
theorem periodFaithfulness_of_holography_of_tomography
    {C : Type u}
    [Category.{v} C]
    (probeFamily : ProbeFamily C)
    (periodInvariant :
      ∀ {X Y : C}, (X ⟶ Y) → Type w)
    (hHolo : Holography probeFamily)
    (hTomo : Tomography probeFamily periodInvariant) :
    PeriodFaithfulness periodInvariant :=
  tomography_implies_periodFaithfulness probeFamily periodInvariant hHolo hTomo

end

end Boundary
