import Boundary.Hodge.HodgeClasses

/-!
# Tate twists for pure Hodge structures and Hodge-number profiles

This file defines the formal Tate twist of a pure rational Hodge structure by
shifting its Hodge pieces and filtration on the same rational carrier. It also
keeps the corresponding bigraded Hodge-number bookkeeping API.

The sign convention is chosen to match the projective-geometric Tate object
already used on the motivic side: one Tate twist lowers the weight by `2` and
shifts Hodge bidegrees by `(-1, -1)`, equivalently
`(H(1))^{p,q} = H^{p+1,q+1}`.
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

/-- The bidegree sum after a Tate twist, written in the source bidegree. -/
theorem tateTwist_pair_sum_eq (p q n : ℤ) :
    (p + n) + (q + n) = (p + q) + 2 * n := by
  rw [show 2 * n = n + n by rw [two_mul]]
  rw [add_assoc]
  rw [show n + (q + n) = q + (n + n) by
    rw [← add_assoc, add_comm n q, add_assoc]]
  rw [← add_assoc]

/-- A weight equality for `H(n)` converted to the corresponding source weight. -/
theorem tateTwist_source_weight_eq {w n p : ℤ} (h : w - 2 * n = 2 * p) :
    w = 2 * (p + n) := by
  calc
    w = w - 2 * n + 2 * n := by rw [sub_add_cancel]
    _ = 2 * p + 2 * n := by rw [h]
    _ = 2 * (p + n) := by rw [mul_add]

/-- A source bidegree sum converted back to the target weight of `H(n)`. -/
theorem tateTwist_target_weight_eq {w p q n : ℤ}
    (h : (p + n) + (q + n) = w) :
    p + q = w - 2 * n := by
  rw [tateTwist_pair_sum_eq] at h
  calc
    p + q = (p + q) + 2 * n - 2 * n := by rw [add_sub_cancel_right]
    _ = w - 2 * n := by rw [h]

namespace PureHodgeStructure

/-- The Tate twist `H(n)` of a pure rational Hodge structure.

With the convention used here, `H(n)^{p,q} = H^{p+n,q+n}` and the weight shifts
from `w` to `w - 2n`. -/
noncomputable def tateTwist (H : PureHodgeStructure) (n : ℤ) : PureHodgeStructure where
  weight := H.weight - 2 * n
  rationalCarrier := H.rationalCarrier
  rationalAddCommGroup := H.rationalAddCommGroup
  rationalModule := H.rationalModule
  rationalFinite := H.rationalFinite
  hodgePiece pq := H.hodgePiece (pq.1 + n, pq.2 + n)
  hodgePiece_free := by
    intro pq
    exact H.hodgePiece_free (pq.1 + n, pq.2 + n)
  hodgePiece_finite := by
    intro pq
    exact H.hodgePiece_finite (pq.1 + n, pq.2 + n)
  hodgeFiltration :=
    { step := fun p => H.hodgeFiltration.step (p + n)
      antitone' := by
        intro p q hpq
        exact H.hodgeFiltration.antitone (add_le_add_right hpq n) }
  oppositeFiltration :=
    { step := fun p => H.oppositeFiltration.step (p + n)
      antitone' := by
        intro p q hpq
        exact H.oppositeFiltration.antitone (add_le_add_right hpq n) }
  piece_le_filtration := by
    intro p r s hpr
    exact H.piece_le_filtration (add_le_add_right hpr n)
  piece_le_oppositeFiltration := by
    intro q r s hqs
    exact H.piece_le_oppositeFiltration (add_le_add_right hqs n)
  filtration_inf_eq := by
    intro p q hpq
    exact
      H.filtration_inf_eq (p := p + n) (q := q + n) (by
        rw [tateTwist_pair_sum_eq, hpq, sub_add_cancel])
  weight_zero := by
    intro p q hpq
    exact H.weight_zero (by
      intro hshift
      apply hpq
      exact tateTwist_target_weight_eq hshift)

@[simp]
theorem tateTwist_weight (H : PureHodgeStructure) (n : ℤ) :
    (H.tateTwist n).weight = H.weight - 2 * n :=
  rfl

@[simp]
theorem tateTwist_hodgePiece (H : PureHodgeStructure) (n p q : ℤ) :
    (H.tateTwist n).hodgePiece (p, q) = H.hodgePiece (p + n, q + n) :=
  rfl

@[simp]
theorem tateTwist_hodgeFiltration_step (H : PureHodgeStructure) (n p : ℤ) :
    (H.tateTwist n).hodgeFiltration.step p = H.hodgeFiltration.step (p + n) :=
  rfl

@[simp]
theorem hodgeNumber_tateTwist (H : PureHodgeStructure) (n p q : ℤ) :
    (H.tateTwist n).hodgeNumber p q = H.hodgeNumber (p + n) (q + n) :=
  rfl

@[simp]
theorem tateTwist_one_weight (H : PureHodgeStructure) :
    (H.tateTwist 1).weight = H.weight - 2 := by
  simp

@[simp]
theorem tateTwist_one_hodgePiece (H : PureHodgeStructure) (p q : ℤ) :
    (H.tateTwist 1).hodgePiece (p, q) = H.hodgePiece (p + 1, q + 1) := by
  simp

@[simp]
theorem rankProfile_tateTwist (H : PureHodgeStructure) (n : ℤ) :
    (H.tateTwist n).rankProfile = twistProfile n H.rankProfile := by
  funext pq
  rcases pq with ⟨p, q⟩
  rfl

theorem isHodgeClass_tateTwist_iff (H : PureHodgeStructure) (n p : ℤ)
    (hweight : (H.tateTwist n).weight = 2 * p)
    (x : H.rationalCarrier) :
    (H.tateTwist n).IsHodgeClass p hweight x ↔
      H.IsHodgeClass (p + n) (by
        rw [tateTwist_weight] at hweight
        exact tateTwist_source_weight_eq hweight) x := by
  rfl

theorem hodgeClasses_tateTwist (H : PureHodgeStructure) (n p : ℤ)
    (hweight : (H.tateTwist n).weight = 2 * p) :
    (H.tateTwist n).hodgeClasses p hweight =
      H.hodgeClasses (p + n) (by
        rw [tateTwist_weight] at hweight
        exact tateTwist_source_weight_eq hweight) := by
  ext x
  exact H.isHodgeClass_tateTwist_iff n p hweight x

theorem isHodgeClass_tateTwist_one_iff (H : PureHodgeStructure) (p : ℤ)
    (hweight : (H.tateTwist 1).weight = 2 * p)
    (x : H.rationalCarrier) :
    (H.tateTwist 1).IsHodgeClass p hweight x ↔
      H.IsHodgeClass (p + 1) (by
        rw [tateTwist_one_weight] at hweight
        exact tateTwist_source_weight_eq hweight) x := by
  exact H.isHodgeClass_tateTwist_iff (1 : ℤ) p hweight x

end PureHodgeStructure

end Hodge
end Boundary
