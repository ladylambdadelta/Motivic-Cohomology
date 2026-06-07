import Mathlib.CategoryTheory.Functor.ReflectsIso
import Boundary.TriangulatedProbes

/-!
# Boundary probe API

This file packages the canonical boundary-facing names for the probe/profile
layer. It deliberately stays close to the owner construction in
`TriangulatedProbes.lean`.

The first theorem target available from the current infrastructure is the
reflection of isomorphisms along the restricted profile functor on a holographic
boundary sector.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe vT uT

namespace Boundary

/-- A canonical boundary probe atom is a single probe datum presented as a
boundary-facing object. -/
abbrev BoundaryProbeAtom (T : Type uT) [Category.{vT} T] [Preadditive T] :=
  ProbeDatum T

/-- A canonical finite boundary probe family: the underlying probe indexing
type is finite. -/
structure BoundaryProbeFamily (T : Type uT) [Category.{vT} T] [Preadditive T] where
  datum : ProbeDatum T
  finiteProbe : Fintype datum.Probe

attribute [instance] BoundaryProbeFamily.finiteProbe

namespace BoundaryProbeFamily

variable {T : Type uT} [Category.{vT} T] [Preadditive T]

/-- The canonical evaluation functor attached to a boundary probe family. -/
abbrev ProbeEvaluation (P : BoundaryProbeFamily T) :=
  P.datum.profileFunctor

end BoundaryProbeFamily

namespace BoundaryProbeFamily

variable {T : Type uT} [Category.{vT} T] [CategoryTheory.Limits.HasZeroObject T]
  [Preadditive T] [HasShift T ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor T n)]
  [Pretriangulated T]

/-- The probe-separable sector determined by a boundary probe family. -/
abbrev ProbeSeparation (P : BoundaryProbeFamily T) (S : TriangulatedSector T) :=
  HolographicProbeFamily T P.datum S

/-- The holographic boundary-sector package. -/
abbrev ProbeHolography (P : BoundaryProbeFamily T) (S : TriangulatedSector T) :=
  HolographicProbeFamily T P.datum S

/-- Global adequacy is currently the same full-and-faithful holographic
condition on the chosen boundary sector. -/
abbrev GlobalAdequacy (P : BoundaryProbeFamily T) (S : TriangulatedSector T) :=
  HolographicProbeFamily T P.datum S

/-- Boundary-facing hom-ext alias for the restricted profile functor. -/
theorem boundaryProbe_hom_ext
    {S : TriangulatedSector T}
    (P : BoundaryProbeFamily T)
    (H : ProbeHolography P S)
    {X Y : S.SectorCategory} {f g : X ⟶ Y}
    (h :
      (restrictedProfileFunctor P.datum S).map f =
        (restrictedProfileFunctor P.datum S).map g) :
    f = g :=
  H.holographic_hom_ext h

/-- Boundary-facing faithfulness alias for the restricted profile functor. -/
theorem boundaryProbe_profile_faithful
    {S : TriangulatedSector T}
    (P : BoundaryProbeFamily T)
    (H : ProbeHolography P S) :
    (restrictedProfileFunctor P.datum S).Faithful := by
  exact H.isFaithful

/-- Boundary-facing iso reflection for morphisms detected by the restricted
profile functor. -/
theorem boundaryProbe_iso_reflects
    {S : TriangulatedSector T}
    (P : BoundaryProbeFamily T)
    (H : ProbeHolography P S)
    {X Y : S.SectorCategory} {f : X ⟶ Y}
    (hf : IsIso ((restrictedProfileFunctor P.datum S).map f)) :
    IsIso f := by
  letI : (restrictedProfileFunctor P.datum S).Full := H.isFull
  letI : (restrictedProfileFunctor P.datum S).Faithful := H.isFaithful
  letI : (restrictedProfileFunctor P.datum S).ReflectsIsomorphisms := by
    infer_instance
  exact isIso_of_reflects_iso f (restrictedProfileFunctor P.datum S)

/- Reflection of isomorphisms along a holographic boundary probe family. -/
def boundaryProbe_separates
    {S : TriangulatedSector T}
    (P : BoundaryProbeFamily T)
    (H : ProbeHolography P S)
    {X Y : S.SectorCategory}
    (h : (restrictedProfileFunctor P.datum S).obj X ≅
      (restrictedProfileFunctor P.datum S).obj Y) :
    X ≅ Y := by
  letI : (restrictedProfileFunctor P.datum S).Full := H.isFull
  letI : (restrictedProfileFunctor P.datum S).Faithful := H.isFaithful
  refine
    { hom := (restrictedProfileFunctor P.datum S).preimage h.hom
      inv := (restrictedProfileFunctor P.datum S).preimage h.inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply (restrictedProfileFunctor P.datum S).map_injective
    rw [Functor.map_comp]
    rw [Functor.map_preimage]
    rw [Functor.map_preimage]
    rw [h.hom_inv_id]
    exact ((restrictedProfileFunctor P.datum S).map_id X).symm
  · apply (restrictedProfileFunctor P.datum S).map_injective
    rw [Functor.map_comp]
    rw [Functor.map_preimage]
    rw [Functor.map_preimage]
    rw [h.inv_hom_id]
    exact ((restrictedProfileFunctor P.datum S).map_id Y).symm

end BoundaryProbeFamily

end Boundary
