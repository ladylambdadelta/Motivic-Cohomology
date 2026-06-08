import Boundary.GeometricMotives

/-!
# MacLane Motives DMgm Compatibility Wrapper

This module re-exports the actual Boundary effective-to-DMgm construction via
formal Tate stabilization, so the historical `MacLane.Motives.DMgm` path
points at the real geometric-motives assembly rather than the generic carrier
alone.
-/

namespace MacLane.Motives

abbrev tatePow := Boundary.Motives.tatePow
abbrev FormalTateStabilizedObject := Boundary.Motives.FormalTateStabilizedObject
abbrev RawTateHomRep := Boundary.Motives.RawTateHomRep
abbrev FormalTateStabilizedHom := Boundary.Motives.FormalTateStabilizedHom
abbrev DMgmQ_Q := Boundary.Motives.DMgmQ_Q

abbrev canonicalGeometricMotives := Boundary.canonicalGeometricMotives
abbrev canonicalGeometricEffectiveToGeometricMotives :=
	Boundary.canonicalGeometricEffectiveToGeometricMotives
abbrev canonicalGeometricMotivesTateShiftEquivalence :=
	Boundary.canonicalGeometricMotivesTateShiftEquivalence

abbrev canonicalBoundaryDMgm := Boundary.canonicalBoundaryDMgm
abbrev canonicalBoundaryDMgmEffectiveEmbedding :=
	Boundary.canonicalBoundaryDMgmEffectiveEmbedding
abbrev canonicalBoundaryDMgmTateShiftEquivalence :=
	Boundary.canonicalBoundaryDMgmTateShiftEquivalence

end MacLane.Motives
