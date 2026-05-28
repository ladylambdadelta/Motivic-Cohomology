import Geometry.Schemes.Basic
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Boundary Objects

Object-layer geometric input for the simplified boundary-first proof strategy.

The goal of this file is modest: define the geometric shapes that will later feed
boundary generation, holography, and tomography, without importing the old trace
calculus vocabulary.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Boundary

/-- Roles played by a boundary probe in the simplified geometric proof. -/
inductive ProbeRole where
  | stratum
  | relative
  | compactSupport
  | overlap
  | residue
  | gysin
  | exceptional
  | specialization
  deriving DecidableEq, Repr

/-- A boundary chart: an ambient smooth scheme together with an open interior. -/
structure BoundaryChart (k : Type u) [Field k] [PerfectField k] where
  ambient : Scheme
  ambientStructMap : ambient ⟶ Spec (CommRingCat.of k)
  ambientProper : IsProper ambientStructMap
  interior : Geometry.SmSchemeOver k
  openEmbedding : interior.scheme ⟶ ambient
  isOpenImmersion : IsOpenImmersion openEmbedding
  denseRange : DenseRange openEmbedding.base

/-- A boundary stratum inside a boundary chart. -/
structure BoundaryStratum (k : Type u) [Field k] [PerfectField k] where
  chart : BoundaryChart k
  support : Scheme
  immersion : support ⟶ chart.ambient
  isClosedImmersion : IsClosedImmersion immersion

/-- A boundary probe is a labeled stratum together with Tate/cohomological shifts. -/
structure BoundaryProbe (k : Type u) [Field k] [PerfectField k] where
  stratum : BoundaryStratum k
  tateTwist : ℤ
  cohomologicalShift : ℤ
  role : ProbeRole

end Boundary
