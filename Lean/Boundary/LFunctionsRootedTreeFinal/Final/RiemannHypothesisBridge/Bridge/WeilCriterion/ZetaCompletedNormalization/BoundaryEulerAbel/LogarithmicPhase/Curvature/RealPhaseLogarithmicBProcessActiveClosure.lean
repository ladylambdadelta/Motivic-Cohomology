import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessFrequencyProducts

/-!
# Closed active-interior B-process estimate

The eight distributed component estimates sum to `83` copies of the balanced
scale.  This owner proves the nonempty bound, weakens it to the round constant
`84`, and joins it with the exactly-zero empty regime.  The resulting theorem
has no mode witness or analytic prerequisite.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun value : ℕ => (value : ℝ)) h)

theorem Real.four_weighted_terms_eq_sum_coeff_mul
    (a b c d x : ℝ) :
    a * x + b * x + c * x + d * x =
      (a + b + c + d) * x := by
  calc
    a * x + b * x + c * x + d * x =
        (a + b) * x + c * x + d * x := by
      exact congrArg (fun value : ℝ => value + c * x + d * x)
        (add_mul a b x).symm
    _ = (a + b + c) * x + d * x := by
      exact congrArg (fun value : ℝ => value + d * x)
        (add_mul (a + b) c x).symm
    _ = (a + b + c + d) * x :=
      (add_mul (a + b + c) d x).symm

theorem Real.three_weighted_terms_eq_sum_coeff_mul
    (a b c x : ℝ) :
    a * x + b * x + c * x = (a + b + c) * x := by
  have hfirst : a * x + b * x = (a + b) * x :=
    (add_mul a b x).symm
  have hwithThird := congrArg (fun value : ℝ => value + c * x) hfirst
  exact Eq.trans hwithThird (add_mul (a + b) c x).symm

theorem Real.two_four_weighted_terms_eq_sum_coeff_mul
    (a b c d e f g h x : ℝ) :
    (a * x + b * x + c * x + d * x) +
        (e * x + f * x + g * x + h * x) =
      ((a + b + c + d) + (e + f + g + h)) * x := by
  have hleft := Real.four_weighted_terms_eq_sum_coeff_mul a b c d x
  have hright := Real.four_weighted_terms_eq_sum_coeff_mul e f g h x
  have hsum := congrArg₂ (fun left right : ℝ => left + right) hleft hright
  exact hsum.trans
    (add_mul (a + b + c + d) (e + f + g + h) x).symm

theorem Real.active_BProcess_coefficient_sum_eq_eighty_three :
    ((3 : ℝ) + 16 + 8 + 16) + (4 + 12 + 12 + 12) = 83 := by
  have hthreeSixteen : (3 : ℝ) + 16 = 19 :=
    realOfNat_add_eq_of_nat_eq 3 16 19 rfl
  have hnineteenEight : (19 : ℝ) + 8 = 27 :=
    realOfNat_add_eq_of_nat_eq 19 8 27 rfl
  have htwentySevenSixteen : (27 : ℝ) + 16 = 43 :=
    realOfNat_add_eq_of_nat_eq 27 16 43 rfl
  have hleft : (3 : ℝ) + 16 + 8 + 16 = 43 :=
    Eq.trans
      (congrArg (fun value : ℝ => value + 8 + 16) hthreeSixteen)
      (Eq.trans
        (congrArg (fun value : ℝ => value + 16) hnineteenEight)
        htwentySevenSixteen)
  have hfourTwelve : (4 : ℝ) + 12 = 16 :=
    realOfNat_add_eq_of_nat_eq 4 12 16 rfl
  have hsixteenTwelve : (16 : ℝ) + 12 = 28 :=
    realOfNat_add_eq_of_nat_eq 16 12 28 rfl
  have htwentyEightTwelve : (28 : ℝ) + 12 = 40 :=
    realOfNat_add_eq_of_nat_eq 28 12 40 rfl
  have hright : (4 : ℝ) + 12 + 12 + 12 = 40 :=
    Eq.trans
      (congrArg (fun value : ℝ => value + 12 + 12) hfourTwelve)
      (Eq.trans
        (congrArg (fun value : ℝ => value + 12) hsixteenTwelve)
        htwentyEightTwelve)
  have hfortyThreeForty : (43 : ℝ) + 40 = 83 :=
    realOfNat_add_eq_of_nat_eq 43 40 83 rfl
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left + right) hleft hright)
    hfortyThreeForty

theorem Real.active_BProcess_weighted_sum_eq_eighty_three
    (x : ℝ) :
    (3 * x + 16 * x + 8 * x + 16 * x) +
        (4 * x + 12 * x + 12 * x + 12 * x) =
      83 * x := by
  have hfactor :=
    Real.two_four_weighted_terms_eq_sum_coeff_mul
      3 16 8 16 4 12 12 12 x
  exact hfactor.trans
    (congrArg (fun coefficient : ℝ => coefficient * x)
      Real.active_BProcess_coefficient_sum_eq_eighty_three)

theorem Real.eighty_three_mul_le_eighty_four_mul
    {x : ℝ} (hx : 0 ≤ x) :
    83 * x ≤ 84 * x := by
  have hcoeff : (83 : ℝ) ≤ 84 := by
    exact Nat.cast_le.mpr (Nat.le_succ 83)
  exact mul_le_mul_of_nonneg_right hcoeff hx

theorem Complex.logarithmicPhaseBProcessClosedInteriorMajorant_le_eighty_three_scale_of_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessClosedInteriorMajorant
        t (a : ℤ) (b : ℤ) ≤
      83 * Complex.logarithmicPhaseBProcessScale t := by
  let S := Complex.logarithmicPhaseBProcessScale t
  let C := Complex.logarithmicPhaseBProcessCrossingScalar
  let L := Complex.logarithmicPhaseBProcessTailScalar t (b : ℤ)
  let M := Complex.logarithmicPhaseBProcessCentralScalar t (b : ℤ)
  let F := Complex.logarithmicPhaseBProcessFrequencyCardScalar t (a : ℤ)
  have hexpand :=
    Complex.logarithmicPhaseBProcessClosedInteriorMajorant_eq_eight_products
      t (a : ℤ) (b : ℤ)
  have hxC : 2 * C ≤ 3 * S :=
    Complex.two_mul_crossingScalar_le_three_mul_scale t
  have hxL : 2 * L ≤ 16 * S :=
    Complex.two_mul_tailScalar_le_sixteen_mul_scale_of_nonempty
      ht hgeometry hnonempty
  have hxM : 2 * M ≤ 8 * S :=
    Complex.two_mul_centralScalar_le_eight_mul_scale_of_nonempty
      ht hgeometry hnonempty
  have hxR : 2 * L ≤ 16 * S := hxL
  have hyC : F * C ≤ 4 * S :=
    Complex.frequencyScalar_mul_crossingScalar_le_four_scale hgeometry
  have hyL : F * L ≤ 12 * S :=
    Complex.frequencyScalar_mul_tailScalar_le_twelve_scale
      ht hgeometry
  have hyM : F * M ≤ 12 * S :=
    Complex.frequencyScalar_mul_centralScalar_le_twelve_scale hgeometry
  have hyR : F * L ≤ 12 * S := hyL
  have hcomponents :=
    Real.distributed_eight_products_le_sum
      hxC hxL hxM hxR hyC hyL hyM hyR
  have hweighted :=
    Real.active_BProcess_weighted_sum_eq_eighty_three S
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ 83 * S)
    hexpand.symm
    (le_trans hcomponents (le_of_eq hweighted))

theorem Complex.logarithmicPhaseBProcessClosedInteriorMajorant_le_eighty_four_scale_of_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessClosedInteriorMajorant
        t (a : ℤ) (b : ℤ) ≤
      84 * Complex.logarithmicPhaseBProcessScale t := by
  have heightyThree :=
    Complex.logarithmicPhaseBProcessClosedInteriorMajorant_le_eighty_three_scale_of_nonempty
      ht hgeometry hnonempty
  have hweaken :=
    Real.eighty_three_mul_le_eighty_four_mul
      (Complex.logarithmicPhaseBProcessScale_nonneg t)
  exact le_trans heightyThree hweaken

theorem Complex.logarithmicPhaseBProcessInteriorBudget_le_eighty_four_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessInteriorBudget
        t (a : ℤ) (b : ℤ) ≤
      84 * Complex.logarithmicPhaseBProcessScale t := by
  have hcases :=
    Complex.logarithmicPhasePoissonBProcessInteriorModes_empty_or_nonempty
      t (a : ℤ) (b : ℤ)
  match hcases with
  | Or.inl hempty =>
      have hzero :=
        Complex.logarithmicPhaseBProcessInteriorBudget_eq_zero_of_empty
          t (a : ℤ) (b : ℤ) hempty
      have hrightNonneg :
          0 ≤ 84 * Complex.logarithmicPhaseBProcessScale t :=
        mul_nonneg (Nat.cast_nonneg 84)
          (Complex.logarithmicPhaseBProcessScale_nonneg t)
      exact Eq.subst
        (motive := fun value : ℝ =>
          value ≤ 84 * Complex.logarithmicPhaseBProcessScale t)
        hzero.symm hrightNonneg
  | Or.inr hnonempty =>
      have hclosed :=
        Complex.logarithmicPhaseBProcessInteriorBudget_le_closedMajorant
          t ht (a : ℤ) (b : ℤ)
          (Int.ofNat_le.mpr
            (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
          (Int.ofNat_zero_le b)
      have harithmetic :=
        Complex.logarithmicPhaseBProcessClosedInteriorMajorant_le_eighty_four_scale_of_nonempty
          ht hgeometry hnonempty
      exact le_trans hclosed harithmetic

theorem Complex.norm_logarithmicPhaseBProcessInterior_packet_tsum_le_eighty_four_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes
          t (a : ℤ) (b : ℤ)},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (a : ℤ) (b : ℤ) m‖ ≤
      84 * Complex.logarithmicPhaseBProcessScale t := by
  have hanalytic :=
    Complex.norm_logarithmicPhaseBProcessInterior_packet_tsum_le_budget
      t ht ht_nonneg (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_order hgeometry))
  have harithmetic :=
    Complex.logarithmicPhaseBProcessInteriorBudget_le_eighty_four_scale
      ht hgeometry
  exact le_trans hanalytic harithmetic

end

end LFunctions
end Boundary
