import Boundary.DMgm
import Boundary.TateMotives

/-!
# Boundary weight generators

This file owns the canonical boundary-facing generator package used by the
weight-structure program. The generators are built from the actual motive
objects already constructed in the Boundary stack:

- the unit / point motive;
- the Tate motive;
- the reduced projective-line cone motive;
- the projective-line motive itself;
- and the Tate shifts of the resulting finite packet.

The file does not postulate a weight structure. It only exports the concrete
generator family and the first boundary-facing membership/closure lemmas.
-/

noncomputable section

open CategoryTheory

universe u

namespace Boundary

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- A boundary weight generator records a concrete object of the stabilized
motivic category together with a boundary-facing tag naming its origin. -/
structure BoundaryWeightGenerator where
  object : VoevodskyDMgmQ_Q (composition := composition)
  tag : String

/-- The canonical unit / point generator. -/
def boundaryUnitPointGenerator : BoundaryWeightGenerator (composition := composition) where
  object :=
    Boundary.Motives.effectiveEmbedding
      (boundaryEffectiveTateObject (composition := composition))
      (Boundary.canonicalUnitMotive composition)
  tag := "unit-point"

/-- The canonical Tate generator. -/
def boundaryTateGenerator : BoundaryWeightGenerator (composition := composition) where
  object := ⟨boundaryEffectiveTateObject (composition := composition), 0⟩
  tag := "tate"

/-- The canonical projective-line generator. -/
def boundaryProjectiveLineGenerator : BoundaryWeightGenerator (composition := composition) where
  object :=
    Boundary.Motives.effectiveEmbedding
      (boundaryEffectiveTateObject (composition := composition))
      (boundaryProjectiveLineMotive (composition := composition))
  tag := "projective-line"

/-- The canonical reduced-cone generator coming from the cone of
`M(Spec k) ⟶ M(P¹)`. -/
def boundaryConeGenerator : BoundaryWeightGenerator (composition := composition) where
  object :=
    Boundary.Motives.effectiveEmbedding
      (boundaryEffectiveTateObject (composition := composition))
      (boundaryReducedProjectiveLineMotive (composition := composition))
  tag := "boundary-cone"

/-- The finite boundary packet of primitive generators used as the seed for the
weight program. -/
def boundaryPrimitivePacketGenerators :
    Finset (BoundaryWeightGenerator (composition := composition)) :=
  { boundaryUnitPointGenerator (composition := composition),
    boundaryTateGenerator (composition := composition),
    boundaryProjectiveLineGenerator (composition := composition),
    boundaryConeGenerator (composition := composition) }

/-- The full finite boundary generator family, including the basic packet and
its Tate-shifted copy. -/
def boundaryWeightGeneratorFamily :
    Finset (BoundaryWeightGenerator (composition := composition)) :=
  boundaryPrimitivePacketGenerators (composition := composition) ∪
    boundaryPrimitivePacketGenerators (composition := composition).image
      (fun g =>
        { object := (Boundary.Motives.tateShift
            (boundaryEffectiveTateObject (composition := composition))).obj g.object
          tag := g.tag ++ "-tate-shift" })

@[simp] theorem boundaryUnitPointGenerator_mem_family :
    boundaryUnitPointGenerator (composition := composition) ∈
      boundaryWeightGeneratorFamily (composition := composition) := by
  unfold boundaryWeightGeneratorFamily boundaryPrimitivePacketGenerators
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert_self _ _))

@[simp] theorem boundaryTateGenerator_mem_family :
    boundaryTateGenerator (composition := composition) ∈
      boundaryWeightGeneratorFamily (composition := composition) := by
  unfold boundaryWeightGeneratorFamily boundaryPrimitivePacketGenerators
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert_self _ _))

@[simp] theorem boundaryProjectiveLineGenerator_mem_family :
    boundaryProjectiveLineGenerator (composition := composition) ∈
      boundaryWeightGeneratorFamily (composition := composition) := by
  unfold boundaryWeightGeneratorFamily boundaryPrimitivePacketGenerators
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert_self _ _))

@[simp] theorem boundaryConeGenerator_mem_family :
    boundaryConeGenerator (composition := composition) ∈
      boundaryWeightGeneratorFamily (composition := composition) := by
  unfold boundaryWeightGeneratorFamily boundaryPrimitivePacketGenerators
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert_self _ _))

/-- A boundary generator family is Tate-closed if every basic generator has its
explicit Tate shift present in the finite family. -/
theorem boundaryWeightGenerators_tateClosed :
    ∀ g : BoundaryWeightGenerator (composition := composition),
      g ∈ boundaryPrimitivePacketGenerators (composition := composition) →
        { object := (Boundary.Motives.tateShift
            (boundaryEffectiveTateObject (composition := composition))).obj g.object
          tag := g.tag ++ "-tate-shift" } ∈
          boundaryWeightGeneratorFamily (composition := composition) := by
  intro g hg
  unfold boundaryWeightGeneratorFamily
  exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨g, hg, rfl⟩))

end Boundary
