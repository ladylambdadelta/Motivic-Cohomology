import Boundary.Hodge.PureHodgeStructure

/-!
# Tate twists for Hodge-number profiles

This file keeps the first Tate layer at the level that is currently canonical:
bigraded Hodge-number bookkeeping.  Constructing the actual one-dimensional
Tate Hodge structure as a complex line can be added after choosing the preferred
line model and conjugation convention.
-/

namespace Boundary
namespace Hodge

/-- The Hodge-number profile of the Tate object `ℚ(n)`: one dimension in
degree `(-n,-n)`. -/
def tateProfile (n : ℤ) : BigradedRankProfile :=
  fun pq => if pq = (-n, -n) then 1 else 0

@[simp]
theorem tateProfile_apply_self (n : ℤ) :
    tateProfile n (-n, -n) = 1 := by
  simp [tateProfile]

theorem tateProfile_apply_ne (n p q : ℤ) (h : (p, q) ≠ (-n, -n)) :
    tateProfile n (p, q) = 0 := by
  simp [tateProfile, h]

/-- Tate twist of a Hodge-number profile. -/
def twistProfile (n : ℤ) (a : BigradedRankProfile) : BigradedRankProfile :=
  BigradedRankProfile.tateTwist n a

@[simp]
theorem twistProfile_apply (n : ℤ) (a : BigradedRankProfile) (p q : ℤ) :
    twistProfile n a (p, q) = a (p + n, q + n) :=
  rfl

@[simp]
theorem twistProfile_zero (a : BigradedRankProfile) :
    twistProfile 0 a = a :=
  BigradedRankProfile.tateTwist_zero a

@[simp]
theorem twistProfile_add (m n : ℤ) (a : BigradedRankProfile) :
    twistProfile m (twistProfile n a) = twistProfile (m + n) a := by
  funext pq
  rcases pq with ⟨p, q⟩
  simp [twistProfile, BigradedRankProfile.tateTwist, add_assoc]

end Hodge
end Boundary
