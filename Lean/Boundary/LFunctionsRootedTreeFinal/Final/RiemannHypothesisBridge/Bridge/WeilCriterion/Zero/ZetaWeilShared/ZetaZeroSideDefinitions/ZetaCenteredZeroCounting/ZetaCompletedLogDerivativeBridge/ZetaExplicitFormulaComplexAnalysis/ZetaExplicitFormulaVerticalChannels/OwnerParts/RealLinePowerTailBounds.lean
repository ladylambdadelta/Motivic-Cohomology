import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Real-line power tail bounds

This file owns neutral one-dimensional power-tail estimates used by vertical
channel arguments.  It is deliberately independent of the zeta explicit
formula: the only analytic content here is the real-variable estimate for
fourth-order Japanese-bracket tails.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- The project fourth-order real-line weight. -/
def realLineFourthOrderWeight (t : ℝ) : ℝ :=
  (1 + ‖t‖) ^ (-(4 : ℤ))

/-- The project inverse-quadratic real-line comparison weight. -/
def realLineInverseQuadraticWeight (T : ℝ) : ℝ :=
  (1 + ‖T‖) ^ (-(2 : ℤ))

/-- Fourth-order Japanese brackets are nonnegative in the project `zpow`
normalization. -/
theorem realLineFourthOrderWeight_nonneg
    (t : ℝ) :
    0 ≤ realLineFourthOrderWeight t :=
  zpow_nonneg (add_nonneg zero_le_one (norm_nonneg t)) (-(4 : ℤ))

/-- Inverse-quadratic Japanese brackets are nonnegative in the project `zpow`
normalization. -/
theorem realLineInverseQuadraticWeight_nonneg
    (T : ℝ) :
    0 ≤ realLineInverseQuadraticWeight T :=
  zpow_nonneg (add_nonneg zero_le_one (norm_nonneg T)) (-(2 : ℤ))

/-- `1 < 4` as an explicit ordered additive fact. -/
theorem realLine_one_lt_four :
    (1 : ℝ) < 4 := by
  exact Nat.one_lt_ofNat

/-- `1 ≤ 3` as an explicit ordered additive fact. -/
theorem realLine_one_le_three :
    (1 : ℝ) ≤ 3 := by
  exact Nat.one_le_ofNat

/-- Pointwise bridge from the project `zpow` convention for fourth-order
Japanese brackets to mathlib's `rpow` convention. -/
theorem realLineFourthOrderWeight_eq_rpow
    (t : ℝ) :
    realLineFourthOrderWeight t =
      (1 + ‖t‖) ^ (-(4 : ℝ)) :=
  by
    unfold realLineFourthOrderWeight
    change (1 + ‖t‖) ^ (-(4 : ℤ)) =
      (1 + ‖t‖) ^ ((-(4 : ℤ) : ℝ))
    exact Eq.trans
      (Real.rpow_intCast (1 + ‖t‖) (-(4 : ℤ))).symm
      (congrArg (fun x : ℝ => (1 + ‖t‖) ^ x) (Int.cast_neg (R := ℝ) 4))

/-- Integrability of the fourth-order real-line weight. -/
theorem realLineFourthOrderWeight_integrable :
    Integrable realLineFourthOrderWeight (volume : Measure ℝ) := by
  have hbase :
    Integrable
        (fun t : ℝ => (1 + ‖t‖) ^ (-(4 : ℝ)))
        (volume : Measure ℝ) :=
    have hfinrank :
        (Module.finrank ℝ ℝ : ℝ) = 1 := by
      exact Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) (Module.finrank_self ℝ))
        (Nat.cast_one)
    integrable_one_add_norm (E := ℝ)
      (show (Module.finrank ℝ ℝ : ℝ) < (4 : ℝ) from
        lt_of_eq_of_lt hfinrank realLine_one_lt_four)
  exact
    hbase.congr
      (Eventually.of_forall
        (fun t => (realLineFourthOrderWeight_eq_rpow t).symm))

/-- Integrability of the fourth-order real-line weight on any measurable set,
as a restriction of the global Japanese-bracket integrability theorem. -/
theorem realLineFourthOrderWeight_integrableOn
    (s : Set ℝ) :
    IntegrableOn realLineFourthOrderWeight s (volume : Measure ℝ) :=
  realLineFourthOrderWeight_integrable.integrableOn

/-- The fourth-order real-line weight is even. -/
theorem realLineFourthOrderWeight_neg
    (t : ℝ) :
    realLineFourthOrderWeight (-t) = realLineFourthOrderWeight t := by
  unfold realLineFourthOrderWeight
  exact congrArg
    (fun r : ℝ => (1 + r) ^ (-(4 : ℤ)))
    (norm_neg t)

/-- Pointwise bridge from the project `zpow` convention for inverse-quadratic
Japanese brackets to mathlib's `rpow` convention. -/
theorem realLineInverseQuadraticWeight_eq_rpow
    (T : ℝ) :
    realLineInverseQuadraticWeight T =
      (1 + ‖T‖) ^ (-(2 : ℝ)) :=
  by
    unfold realLineInverseQuadraticWeight
    change (1 + ‖T‖) ^ (-(2 : ℤ)) =
      (1 + ‖T‖) ^ ((-(2 : ℤ) : ℝ))
    exact Eq.trans
      (Real.rpow_intCast (1 + ‖T‖) (-(2 : ℤ))).symm
      (congrArg (fun x : ℝ => (1 + ‖T‖) ^ x) (Int.cast_neg (R := ℝ) 2))

/-- The complement of the symmetric closed interval is the union of the two
open tails. -/
theorem realLine_compl_Icc_eq_leftRightTail_union
    (T : ℝ) :
    (Set.Icc (-T) T)ᶜ = Set.Iio (-T) ∪ Set.Ioi T := by
  ext t
  constructor
  · intro ht
    by_cases hleft : t < -T
    · exact Or.inl hleft
    · exact Or.inr (lt_of_not_ge fun hright ↦ ht ⟨le_of_not_gt hleft, hright⟩)
  · intro ht hmem
    match ht with
    | Or.inl hleft => exact (not_le_of_gt hleft) hmem.1
    | Or.inr hright => exact (not_le_of_gt hright) hmem.2

/-- On the right tail, the fourth-order Japanese bracket is bounded by the
bare power tail used by `integral_Ioi_rpow_of_lt`. -/
theorem realLineFourthOrderWeight_le_rpow_on_Ioi_of_one_le
    {T t : ℝ}
    (hT : 1 ≤ T)
    (ht : t ∈ Set.Ioi T) :
    realLineFourthOrderWeight t ≤ t ^ (-(4 : ℝ)) := by
  have ht_pos : 0 < t := lt_trans zero_lt_one (hT.trans_lt ht)
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  have ht_norm : ‖t‖ = t := Real.norm_of_nonneg ht_nonneg
  have ht_le_one_add_norm : t ≤ 1 + ‖t‖ := by
    calc
      t = 0 + t := (zero_add t).symm
      _ ≤ 1 + t := add_le_add_right zero_le_one t
      _ = 1 + ‖t‖ := congrArg (fun u : ℝ ↦ 1 + u) ht_norm.symm
  have ht_rpow :
      (1 + ‖t‖) ^ (-(4 : ℝ)) ≤ t ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ht_pos ht_le_one_add_norm
      (neg_nonpos.mpr (show (0 : ℝ) ≤ 4 from zero_le_four))
  exact (le_of_eq (realLineFourthOrderWeight_eq_rpow t)).trans ht_rpow

/-- The exponent in the fourth-power tail primitive normalizes to `-3`. -/
theorem realLine_neg_four_add_one_eq_neg_three :
    (-(4 : ℝ)) + 1 = -(3 : ℝ) :=
  calc
    (-(4 : ℝ)) + 1 = (-(3 : ℝ) + -(1 : ℝ)) + 1 := by
      exact congrArg (fun x : ℝ => x + 1) (by
        calc
          (-(4 : ℝ)) = -((3 : ℝ) + (1 : ℝ)) := by
            exact congrArg Neg.neg
              (Eq.trans
                (Eq.trans
                  (show (4 : ℝ) = ((3 + 1 : ℕ) : ℝ) from Eq.refl _)
                  (Nat.cast_add (R := ℝ) 3 1))
                (congrArg₂
                  (fun x y : ℝ => x + y)
                  (Nat.cast_ofNat (R := ℝ) (n := 3))
                  Nat.cast_one))
          _ = -(3 : ℝ) + -(1 : ℝ) := neg_add 3 1)
    _ = -(3 : ℝ) := neg_add_cancel_right (-(3 : ℝ)) (1 : ℝ)

/-- Dividing a negated scalar by `-3` is multiplication by `1 / 3`. -/
theorem realLine_neg_div_neg_three_eq_one_div_three_mul
    (a : ℝ) :
    -a / (-(3 : ℝ)) = (1 / 3 : ℝ) * a :=
  Eq.trans
    (neg_div_neg_eq a (3 : ℝ))
    (Eq.symm (one_div_mul_eq_div (a := (3 : ℝ)) (b := a)))

/-- Product-of-inverses normalization for the constant `3`. -/
theorem realLine_one_div_three_mul_inv_eq_inv_three_mul
    (a : ℝ) :
    (1 / 3 : ℝ) * a⁻¹ = (3 * a)⁻¹ := by
  calc
    (1 / 3 : ℝ) * a⁻¹ = 3⁻¹ * a⁻¹ := by
      exact congrArg (fun x : ℝ => x * a⁻¹) (one_div 3)
    _ = (a * 3)⁻¹ := by
      exact Eq.symm (mul_inv_rev a 3)
    _ = (3 * a)⁻¹ := by
      exact congrArg Inv.inv (mul_comm a 3)

/-- Positive `T` turns the normalized inverse-cubic `rpow` into a reciprocal
ordinary cube. -/
theorem realLine_one_div_three_mul_rpow_neg_three_eq_inv_three_mul_cube
    {T : ℝ} (hT_nonneg : 0 ≤ T) :
    (1 / 3 : ℝ) * T ^ (-(3 : ℝ)) = (3 * T ^ 3)⁻¹ := by
  have hrpow :
      T ^ (-(3 : ℝ)) = (T ^ (3 : ℝ))⁻¹ :=
    Real.rpow_neg hT_nonneg (3 : ℝ)
  have hnat :
      T ^ (3 : ℝ) = T ^ 3 :=
    Real.rpow_natCast T 3
  calc
    (1 / 3 : ℝ) * T ^ (-(3 : ℝ))
        = (1 / 3 : ℝ) * (T ^ (3 : ℝ))⁻¹ := by
          exact congrArg (fun x : ℝ => (1 / 3 : ℝ) * x) hrpow
    _ = (1 / 3 : ℝ) * (T ^ 3)⁻¹ := by
          exact congrArg (fun x : ℝ => (1 / 3 : ℝ) * x⁻¹) hnat
    _ = (3 * T ^ 3)⁻¹ := by
          exact realLine_one_div_three_mul_inv_eq_inv_three_mul (T ^ 3)

/-- `4 ≤ 9` as an ordered fact, named to avoid arithmetic automation in
tail arithmetic. -/
theorem realLine_four_le_nine :
    (4 : ℝ) ≤ 9 := by
  have hone_nonneg : (0 : ℝ) ≤ 1 := zero_le_one
  have hfour_le_six :
      (4 : ℝ) ≤ 6 := by
    calc
        (4 : ℝ) = 4 + 0 := (add_zero 4).symm
        _ ≤ 4 + 2 := add_le_add_left (show (0 : ℝ) ≤ 2 from zero_le_two) 4
        _ = 6 := (Nat.cast_add (R := ℝ) 4 2).symm
  have hsix_le_nine :
      (6 : ℝ) ≤ 9 := by
    calc
        (6 : ℝ) = 6 + 0 := (add_zero 6).symm
        _ ≤ 6 + 3 := add_le_add_left (le_of_lt (show (0 : ℝ) < 3 from zero_lt_three)) 6
        _ = 9 := (Nat.cast_add (R := ℝ) 6 3).symm
  exact hfour_le_six.trans hsix_le_nine

/-- A positive base raised to `-2` as an `rpow` is the inverse of its square. -/
theorem realLine_rpow_neg_two_eq_inv_sq
    {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ :=
  Eq.trans
    (Real.rpow_neg hx (2 : ℝ))
    (congrArg Inv.inv (Real.rpow_natCast x 2))

/-- A crude polynomial comparison sufficient for the real-line tail:
`(1 + T)^2 ≤ 3T^3` for `T ≥ 3`. -/
theorem realLine_one_add_sq_le_three_mul_cube_of_three_le
    {T : ℝ} (hT : 3 ≤ T) :
    (1 + T) ^ 2 ≤ 3 * T ^ 3 := by
  have hT_nonneg : 0 ≤ T := (le_of_lt zero_lt_three).trans hT
  have hT_ge_one : 1 ≤ T := realLine_one_le_three.trans hT
  have h_one_add_le_two_mul : 1 + T ≤ 2 * T := by
    calc
      1 + T ≤ T + T := add_le_add_right hT_ge_one T
      _ = 2 * T := (two_mul T).symm
  have hsquare_le :
      (1 + T) ^ 2 ≤ (2 * T) ^ 2 :=
    pow_le_pow_left₀ (add_nonneg zero_le_one hT_nonneg)
      h_one_add_le_two_mul 2
  have h_four_mul_sq_le_three_mul_cube :
      (2 * T) ^ 2 ≤ 3 * T ^ 3 := by
    have hT_sq_nonneg : 0 ≤ T ^ 2 := sq_nonneg T
    have hfourT2 :
        (2 * T) ^ 2 = 4 * T ^ 2 := by
      calc
        (2 * T) ^ 2 = (2 * T) * (2 * T) := pow_two (2 * T)
        _ = (2 * 2) * (T * T) := by
          exact mul_mul_mul_comm 2 T 2 T
        _ = 4 * (T * T) := by
            exact congrArg (fun x : ℝ => x * (T * T)) (show (2 : ℝ) * 2 = 4 from
              Eq.trans
                (Nat.cast_mul (α := ℝ) 2 2).symm
                (show (((2 * 2 : ℕ) : ℝ)) = 4 from Eq.refl _))
        _ = 4 * T ^ 2 := by
          exact congrArg (fun x : ℝ => 4 * x) (Eq.symm (pow_two T))
    have hfour_le_threeT : (4 : ℝ) ≤ 3 * T := by
      calc
        (4 : ℝ) ≤ 9 := realLine_four_le_nine
        _ = 3 * 3 := Eq.trans
          (show (9 : ℝ) = ((3 * 3 : ℕ) : ℝ) from Eq.refl _)
          (Nat.cast_mul (α := ℝ) 3 3)
        _ ≤ 3 * T := mul_le_mul_of_nonneg_left hT (le_of_lt zero_lt_three)
    calc
      (2 * T) ^ 2 = 4 * T ^ 2 := hfourT2
      _ ≤ (3 * T) * T ^ 2 := mul_le_mul_of_nonneg_right hfour_le_threeT hT_sq_nonneg
      _ = 3 * T ^ 3 := by
        calc
          (3 * T) * T ^ 2 = 3 * (T * T ^ 2) := mul_assoc 3 T (T ^ 2)
          _ = 3 * T ^ 3 := by
              exact congrArg (fun x : ℝ => 3 * x)
                (pow_succ' T 2).symm
  exact hsquare_le.trans h_four_mul_sq_le_three_mul_cube

/-- Arithmetic normalization of the fourth-power tail primitive at a positive
endpoint. -/
theorem realLine_bareFourthPower_Ioi_tail_eval_normalized
    {T : ℝ}
    (hT_pos : 0 < T)
    (h_eval :
      ∫ t in Set.Ioi T, t ^ (-(4 : ℝ)) =
        -T ^ ((-(4 : ℝ)) + 1) / ((-(4 : ℝ)) + 1)) :
    ∫ t in Set.Ioi T, t ^ (-(4 : ℝ)) =
      (1 / 3) * T ^ (-(3 : ℝ)) := by
  calc
    ∫ t in Set.Ioi T, t ^ (-(4 : ℝ))
        = -T ^ ((-(4 : ℝ)) + 1) / ((-(4 : ℝ)) + 1) := h_eval
    _ = -T ^ (-(3 : ℝ)) / (-(3 : ℝ)) := by
      exact congrArg
        (fun x : ℝ => -T ^ x / x)
        realLine_neg_four_add_one_eq_neg_three
    _ = (1 / 3) * T ^ (-(3 : ℝ)) :=
      realLine_neg_div_neg_three_eq_one_div_three_mul (T ^ (-(3 : ℝ)))

/-- For `T ≥ 3`, the normalized fourth-power right tail is bounded by the
inverse-quadratic Japanese bracket in `rpow` form. -/
theorem realLine_bareFourthPower_normalized_tail_le_inverseQuadratic_rpow
    {T : ℝ}
    (hT : 3 ≤ T) :
    (1 / 3 : ℝ) * T ^ (-(3 : ℝ)) ≤ (1 + ‖T‖) ^ (-(2 : ℝ)) := by
  have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_three hT
  have hT_nonneg : 0 ≤ T := le_of_lt hT_pos
  have hT_norm : ‖T‖ = T := Real.norm_of_nonneg hT_nonneg
  have hbase_pos : 0 < 1 + ‖T‖ := add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg T)
  have hden_pos : 0 < 3 * T ^ 3 :=
    mul_pos zero_lt_three (pow_pos hT_pos 3)
  have hbracket_sq_pos : 0 < (1 + ‖T‖) ^ 2 :=
    pow_pos hbase_pos 2
  have hden_le :
      (1 + ‖T‖) ^ 2 ≤ 3 * T ^ 3 := by
    exact Eq.subst
      (motive := fun x : ℝ => (1 + x) ^ 2 ≤ 3 * T ^ 3)
      hT_norm.symm
      (realLine_one_add_sq_le_three_mul_cube_of_three_le hT)
  have hinv_le :
      (3 * T ^ 3)⁻¹ ≤ ((1 + ‖T‖) ^ 2)⁻¹ :=
    inv_le_inv_of_le hbracket_sq_pos hden_le
  have hleft_eq :
      (1 / 3 : ℝ) * T ^ (-(3 : ℝ)) = (3 * T ^ 3)⁻¹ := by
    exact realLine_one_div_three_mul_rpow_neg_three_eq_inv_three_mul_cube
      hT_nonneg
  have hright_eq :
      (1 + ‖T‖) ^ (-(2 : ℝ)) = ((1 + ‖T‖) ^ 2)⁻¹ := by
    exact realLine_rpow_neg_two_eq_inv_sq (le_of_lt hbase_pos)
  exact (le_of_eq hleft_eq).trans (hinv_le.trans (le_of_eq hright_eq.symm))

/-- The one-sided bare fourth-power tail is bounded by the inverse-quadratic
Japanese bracket after a fixed threshold. -/
theorem realLine_bareFourthPower_Ioi_tail_eventually_le_inverseQuadratic :
    ∀ᶠ T in atTop,
      ∫ t in Set.Ioi T, t ^ (-(4 : ℝ))
        ≤ realLineInverseQuadraticWeight T := by
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
  have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_three hT
  have h_eval :
      ∫ t in Set.Ioi T, t ^ (-(4 : ℝ)) = -T ^ ((-(4 : ℝ)) + 1) / ((-(4 : ℝ)) + 1) :=
    integral_Ioi_rpow_of_lt
      (neg_lt_neg realLine_one_lt_four) hT_pos
  have h_tail :
      ∫ t in Set.Ioi T, t ^ (-(4 : ℝ)) = (1 / 3) * T ^ (-(3 : ℝ)) := by
    exact realLine_bareFourthPower_Ioi_tail_eval_normalized hT_pos h_eval
  have h_compare :
      (1 / 3 : ℝ) * T ^ (-(3 : ℝ)) ≤ (1 + ‖T‖) ^ (-(2 : ℝ)) := by
    exact realLine_bareFourthPower_normalized_tail_le_inverseQuadratic_rpow hT
  exact (le_of_eq h_tail).trans
    (h_compare.trans (le_of_eq (realLineInverseQuadraticWeight_eq_rpow T).symm))

/-- Right-tail estimate for the project fourth-order weight. -/
theorem realLineFourthOrderWeight_Ioi_tail_eventually_le_inverseQuadratic :
    ∀ᶠ T in atTop,
      ∫ t in Set.Ioi T, realLineFourthOrderWeight t
        ≤ realLineInverseQuadraticWeight T := by
  filter_upwards
    [eventually_ge_atTop (1 : ℝ),
      realLine_bareFourthPower_Ioi_tail_eventually_le_inverseQuadratic] with T hT htail
  have h_integrable :
    IntegrableOn (fun t : ℝ ↦ t ^ (-(4 : ℝ))) (Set.Ioi T) :=
    integrableOn_Ioi_rpow_of_lt
      (neg_lt_neg realLine_one_lt_four)
      (lt_of_lt_of_le zero_lt_one hT)
  have h_mono :
      ∫ t in Set.Ioi T, realLineFourthOrderWeight t
        ≤ ∫ t in Set.Ioi T, t ^ (-(4 : ℝ)) := by
    have h_weight_integrable :
        IntegrableOn realLineFourthOrderWeight (Set.Ioi T) (volume : Measure ℝ) :=
      realLineFourthOrderWeight_integrableOn (Set.Ioi T)
    exact
      MeasureTheory.setIntegral_mono_on
        h_weight_integrable h_integrable measurableSet_Ioi
        (fun t ht =>
          realLineFourthOrderWeight_le_rpow_on_Ioi_of_one_le hT ht)
  exact h_mono.trans htail

/-- Reflection sends the left fourth-order tail to the right fourth-order tail. -/
theorem realLineFourthOrderWeight_Iio_tail_eq_Ioi_tail
    (T : ℝ) :
    ∫ t in Set.Iio (-T), realLineFourthOrderWeight t
      = ∫ t in Set.Ioi T, realLineFourthOrderWeight t := by
  have hcomp :
      (∫ t in Set.Ioi T, realLineFourthOrderWeight (-t)) =
        ∫ t in Set.Iic (-T), realLineFourthOrderWeight t :=
    integral_comp_neg_Ioi T realLineFourthOrderWeight
  have hendpoint :
      (∫ t in Set.Iic (-T), realLineFourthOrderWeight t) =
        ∫ t in Set.Iio (-T), realLineFourthOrderWeight t :=
    integral_Iic_eq_integral_Iio
  have heven_integral :
      (∫ t in Set.Ioi T, realLineFourthOrderWeight (-t)) =
        ∫ t in Set.Ioi T, realLineFourthOrderWeight t := by
    have hfun :
        (fun t : ℝ => realLineFourthOrderWeight (-t)) =
          fun t : ℝ => realLineFourthOrderWeight t := by
      funext t
      exact realLineFourthOrderWeight_neg t
    exact congrArg
      (fun φ : ℝ → ℝ => ∫ t in Set.Ioi T, φ t)
      hfun
  exact (hcomp.trans hendpoint).symm.trans heven_integral

/-- Both open fourth-order tails together satisfy the inverse-quadratic bound
with constant `2`. -/
theorem realLineFourthOrderWeight_leftRightTail_union_eventually_le_two_inverseQuadratic :
    ∀ᶠ T in atTop,
      ∫ t in Set.Iio (-T) ∪ Set.Ioi T, realLineFourthOrderWeight t
        ≤ 2 * realLineInverseQuadraticWeight T := by
  filter_upwards
    [eventually_ge_atTop (0 : ℝ),
      realLineFourthOrderWeight_Ioi_tail_eventually_le_inverseQuadratic] with T hT_nonneg hright
  have hleft :
      ∫ t in Set.Iio (-T), realLineFourthOrderWeight t
        ≤ realLineInverseQuadraticWeight T :=
    (le_of_eq (realLineFourthOrderWeight_Iio_tail_eq_Ioi_tail T)).trans hright
  have h_integrable_left :
      IntegrableOn realLineFourthOrderWeight (Set.Iio (-T)) := by
    exact realLineFourthOrderWeight_integrableOn (Set.Iio (-T))
  have h_integrable_right :
      IntegrableOn realLineFourthOrderWeight (Set.Ioi T) := by
    exact realLineFourthOrderWeight_integrableOn (Set.Ioi T)
  have h_union :
      ∫ t in Set.Iio (-T) ∪ Set.Ioi T, realLineFourthOrderWeight t
        =
          (∫ t in Set.Iio (-T), realLineFourthOrderWeight t)
            + (∫ t in Set.Ioi T, realLineFourthOrderWeight t) :=
    let hneg_le : -T ≤ T := neg_le_self hT_nonneg
    let hdisjoint : Disjoint (Set.Iio (-T)) (Set.Ioi T) :=
      Set.disjoint_left.2
        (fun t ht_left ht_right =>
          not_lt_of_ge hneg_le (lt_trans ht_right ht_left))
    setIntegral_union hdisjoint measurableSet_Ioi h_integrable_left h_integrable_right
  calc
    ∫ t in Set.Iio (-T) ∪ Set.Ioi T, realLineFourthOrderWeight t
        =
          (∫ t in Set.Iio (-T), realLineFourthOrderWeight t)
            + (∫ t in Set.Ioi T, realLineFourthOrderWeight t) := h_union
    _ ≤ realLineInverseQuadraticWeight T + realLineInverseQuadraticWeight T :=
      add_le_add hleft hright
    _ = 2 * realLineInverseQuadraticWeight T :=
      (two_mul (realLineInverseQuadraticWeight T)).symm

/-- Core real-variable tail estimate for the fourth-order Japanese bracket.

This is the neutral calculus theorem
`∫_{|t| > T} (1 + |t|)^{-4} dt = O((1 + |T|)^{-2})`.
The proof should split the complement into the two open tails, use the
substitution `t ↦ -t` on the left tail, compare `(1 + t)^{-4}` on the right
tail to an integrable power tail, and evaluate that tail with
`integral_Ioi_rpow_of_lt`. -/
theorem realLineFourthOrderWeight_compl_Icc_tail_eventually_le_inverseQuadratic :
    ∃ C : ℝ,
      0 < C ∧
        ∀ᶠ T in atTop,
          ∫ t in (Set.Icc (-T) T)ᶜ, realLineFourthOrderWeight t
            ≤ C * realLineInverseQuadraticWeight T := by
  refine ⟨2, zero_lt_two, ?_⟩
  filter_upwards
    [realLineFourthOrderWeight_leftRightTail_union_eventually_le_two_inverseQuadratic] with T hT
  exact (le_of_eq (congrArg
    (fun s : Set ℝ ↦ ∫ t in s, realLineFourthOrderWeight t)
    (realLine_compl_Icc_eq_leftRightTail_union T))).trans hT

end
end LFunctions
end Boundary
