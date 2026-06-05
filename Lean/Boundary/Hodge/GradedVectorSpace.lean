import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Graded vector-space dimension profiles

This file records the finite-dimensional bookkeeping used by the Hodge-number
API.  It deliberately keeps the structure at the level of graded pieces rather
than pretending to construct direct-sum decompositions of a total space.
-/

universe u v

namespace Boundary
namespace Hodge

variable (K : Type u) [Field K]

/-- A family of finite-dimensional vector spaces indexed by `ι`. -/
structure GradedVectorSpace (ι : Type v) where
  piece : ι → Type u
  addCommGroup : ∀ i, AddCommGroup (piece i)
  module : ∀ i, Module K (piece i)
  free : ∀ i, Module.Free K (piece i)
  finite : ∀ i, Module.Finite K (piece i)

namespace GradedVectorSpace

attribute [instance] addCommGroup module free finite

variable {K}
variable {ι : Type v}

/-- The dimension of a graded piece. -/
noncomputable def rank (G : GradedVectorSpace K ι) (i : ι) : ℕ :=
  Module.finrank K (G.piece i)

/-- Pointwise product of graded vector spaces. -/
def prod (G H : GradedVectorSpace K ι) : GradedVectorSpace K ι where
  piece := fun i => G.piece i × H.piece i
  addCommGroup := fun _ => inferInstance
  module := fun _ => inferInstance
  free := fun i => by
    letI := G.free i
    letI := H.free i
    infer_instance
  finite := fun i => by
    letI := G.free i
    letI := H.free i
    letI := G.finite i
    letI := H.finite i
    infer_instance

@[simp]
theorem rank_prod (G H : GradedVectorSpace K ι) (i : ι) :
    rank (G.prod H) i = rank G i + rank H i := by
  letI := G.finite i
  letI := H.finite i
  letI := G.free i
  letI := H.free i
  simp [rank, prod, Module.finrank_prod]

end GradedVectorSpace

/-- A bare integer-indexed dimension profile. -/
abbrev BigradedRankProfile := ℤ × ℤ → ℕ

namespace BigradedRankProfile

/-- Pointwise sum of bigraded rank profiles. -/
def add (a b : BigradedRankProfile) : BigradedRankProfile :=
  fun pq => a pq + b pq

/-- Tate twist of a bigraded rank profile: `(p,q)` in the twist is
`(p + n, q + n)` before twisting. -/
def tateTwist (n : ℤ) (a : BigradedRankProfile) : BigradedRankProfile :=
  fun pq => a (pq.1 + n, pq.2 + n)

/-- Dual rank profile, reversing bidegrees. -/
def dual (a : BigradedRankProfile) : BigradedRankProfile :=
  fun pq => a (-pq.1, -pq.2)

@[simp]
theorem add_apply (a b : BigradedRankProfile) (pq : ℤ × ℤ) :
    add a b pq = a pq + b pq :=
  rfl

@[simp]
theorem tateTwist_apply (n : ℤ) (a : BigradedRankProfile) (p q : ℤ) :
    tateTwist n a (p, q) = a (p + n, q + n) :=
  rfl

@[simp]
theorem dual_apply (a : BigradedRankProfile) (p q : ℤ) :
    dual a (p, q) = a (-p, -q) :=
  rfl

@[simp]
theorem dual_dual (a : BigradedRankProfile) : dual (dual a) = a := by
  funext pq
  rcases pq with ⟨p, q⟩
  simp [dual]

@[simp]
theorem tateTwist_zero (a : BigradedRankProfile) : tateTwist 0 a = a := by
  funext pq
  rcases pq with ⟨p, q⟩
  simp [tateTwist]

end BigradedRankProfile

end Hodge
end Boundary
