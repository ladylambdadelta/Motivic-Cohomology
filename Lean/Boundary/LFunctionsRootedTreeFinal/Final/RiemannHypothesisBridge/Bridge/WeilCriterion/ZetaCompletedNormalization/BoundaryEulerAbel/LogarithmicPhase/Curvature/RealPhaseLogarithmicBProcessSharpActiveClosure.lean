import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessActiveClosure

/-!
# Sharpened active-interior B-process closure

The first closed checkpoint retained an unnecessary factor two in the
nonempty endpoint-tail comparison.  This owner keeps the exact cancellation
`(2‖t‖)S / ‖t‖ = 2S`.  Each additive-cardinality tail product is therefore at
most `8S`, reducing the complete active coefficient from `83` to `67`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun value : ℕ => (value : ℝ)) h)

private theorem realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun value : ℕ => (value : ℝ)) h)

private theorem real_two_mul_two_eq_four :
    (2 : ℝ) * 2 = 4 :=
  realOfNat_mul_eq_of_nat_eq 2 2 4 rfl

private theorem real_four_mul_two_eq_eight :
    (4 : ℝ) * 2 = 8 :=
  realOfNat_mul_eq_of_nat_eq 4 2 8 rfl

theorem Real.longGeometry_blockRight_mul_scale_div_norm_le_two_mul_scale_of_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    (b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ ≤
      2 * Complex.logarithmicPhaseBProcessScale t := by
  have hbNorm :=
    Complex.logarithmicPhaseBProcess_natBlockRight_le_two_mul_norm_of_nonempty
      t ht
      (Real.logarithmicPhaseLongBranchGeometry_comparable hgeometry)
      hnonempty
  have hmul := mul_le_mul_of_nonneg_right hbNorm
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have hnormPos := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hdiv := div_le_div_of_nonneg_right hmul hnormPos.le
  have hcancel :
      (2 * ‖t‖) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ =
        2 * Complex.logarithmicPhaseBProcessScale t := by
    calc
      (2 * ‖t‖) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ =
          (2 * Complex.logarithmicPhaseBProcessScale t) * ‖t‖ / ‖t‖ := by
        exact congrArg (fun value : ℝ => value / ‖t‖)
          (calc
            (2 * ‖t‖) * Complex.logarithmicPhaseBProcessScale t =
                2 * (‖t‖ * Complex.logarithmicPhaseBProcessScale t) :=
              mul_assoc 2 ‖t‖ _
            _ = 2 * (Complex.logarithmicPhaseBProcessScale t * ‖t‖) :=
              congrArg (fun value : ℝ => 2 * value) (mul_comm _ _)
            _ = (2 * Complex.logarithmicPhaseBProcessScale t) * ‖t‖ :=
              (mul_assoc 2 _ ‖t‖).symm)
      _ = 2 * Complex.logarithmicPhaseBProcessScale t :=
        mul_div_cancel_right₀ _ (ne_of_gt hnormPos)
  exact le_trans hdiv (le_of_eq hcancel)

theorem Complex.two_mul_tailScalar_le_eight_mul_scale_of_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    2 * Complex.logarithmicPhaseBProcessTailScalar t (b : ℤ) ≤
      8 * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessTailScalar
  have hbase :=
    Real.longGeometry_blockRight_mul_scale_div_norm_le_two_mul_scale_of_nonempty
      ht hgeometry hnonempty
  have hfourNonneg : (0 : ℝ) ≤ 4 := Nat.cast_nonneg 4
  have hscaled := mul_le_mul_of_nonneg_left hbase hfourNonneg
  have hleft :
      2 * (2 * ((b : ℝ) *
        Complex.logarithmicPhaseBProcessScale t / ‖t‖)) =
        4 * ((b : ℝ) *
          Complex.logarithmicPhaseBProcessScale t / ‖t‖) := by
    exact Eq.trans (mul_assoc 2 2 _).symm
      (congrArg
        (fun value : ℝ => value *
          ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖))
        real_two_mul_two_eq_four)
  have hright :
      4 * (2 * Complex.logarithmicPhaseBProcessScale t) =
        8 * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans (mul_assoc 4 2 _).symm
      (congrArg
        (fun value : ℝ =>
          value * Complex.logarithmicPhaseBProcessScale t)
        real_four_mul_two_eq_eight)
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤ 8 * Complex.logarithmicPhaseBProcessScale t)
    hleft.symm
    (Eq.subst
      (motive := fun value : ℝ =>
        4 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) ≤ value)
      hright hscaled)

theorem Real.sharp_active_BProcess_coefficient_sum_eq_sixty_seven :
    ((3 : ℝ) + 8 + 8 + 8) + (4 + 12 + 12 + 12) = 67 := by
  have hthreeEight : (3 : ℝ) + 8 = 11 :=
    realOfNat_add_eq_of_nat_eq 3 8 11 rfl
  have helevenEight : (11 : ℝ) + 8 = 19 :=
    realOfNat_add_eq_of_nat_eq 11 8 19 rfl
  have hnineteenEight : (19 : ℝ) + 8 = 27 :=
    realOfNat_add_eq_of_nat_eq 19 8 27 rfl
  have hleft : (3 : ℝ) + 8 + 8 + 8 = 27 :=
    Eq.trans
      (congrArg (fun value : ℝ => value + 8 + 8) hthreeEight)
      (Eq.trans
        (congrArg (fun value : ℝ => value + 8) helevenEight)
        hnineteenEight)
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
  have htwentySevenForty : (27 : ℝ) + 40 = 67 :=
    realOfNat_add_eq_of_nat_eq 27 40 67 rfl
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left + right) hleft hright)
    htwentySevenForty

theorem Real.sharp_active_BProcess_weighted_sum_eq_sixty_seven
    (x : ℝ) :
    (3 * x + 8 * x + 8 * x + 8 * x) +
        (4 * x + 12 * x + 12 * x + 12 * x) =
      67 * x := by
  have hfactor :=
    Real.two_four_weighted_terms_eq_sum_coeff_mul
      3 8 8 8 4 12 12 12 x
  exact hfactor.trans
    (congrArg (fun coefficient : ℝ => coefficient * x)
      Real.sharp_active_BProcess_coefficient_sum_eq_sixty_seven)

theorem Real.sixty_seven_mul_le_sixty_eight_mul
    {x : ℝ} (hx : 0 ≤ x) :
    67 * x ≤ 68 * x := by
  have hcoeff : (67 : ℝ) ≤ 68 :=
    Nat.cast_le.mpr (Nat.le_succ 67)
  exact mul_le_mul_of_nonneg_right hcoeff hx

theorem Complex.logarithmicPhaseBProcessClosedInteriorMajorant_le_sixty_seven_scale_of_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessClosedInteriorMajorant
        t (a : ℤ) (b : ℤ) ≤
      67 * Complex.logarithmicPhaseBProcessScale t := by
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
  have hxL : 2 * L ≤ 8 * S :=
    Complex.two_mul_tailScalar_le_eight_mul_scale_of_nonempty
      ht hgeometry hnonempty
  have hxM : 2 * M ≤ 8 * S :=
    Complex.two_mul_centralScalar_le_eight_mul_scale_of_nonempty
      ht hgeometry hnonempty
  have hyC : F * C ≤ 4 * S :=
    Complex.frequencyScalar_mul_crossingScalar_le_four_scale hgeometry
  have hyL : F * L ≤ 12 * S :=
    Complex.frequencyScalar_mul_tailScalar_le_twelve_scale ht hgeometry
  have hyM : F * M ≤ 12 * S :=
    Complex.frequencyScalar_mul_centralScalar_le_twelve_scale hgeometry
  have hsharpComponents :
      (2 * C + 2 * L + 2 * M + 2 * L) +
          (F * C + F * L + F * M + F * L) ≤
        (3 * S + 8 * S + 8 * S + 8 * S) +
          (4 * S + 12 * S + 12 * S + 12 * S) := by
    exact Real.add_two_four_term_bounds
      hxC hxL hxM hxL hyC hyL hyM hyL
  have hweighted :=
    Real.sharp_active_BProcess_weighted_sum_eq_sixty_seven S
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ 67 * S)
    hexpand.symm
    (le_trans hsharpComponents (le_of_eq hweighted))

theorem Complex.logarithmicPhaseBProcessInteriorBudget_le_sixty_eight_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessInteriorBudget
        t (a : ℤ) (b : ℤ) ≤
      68 * Complex.logarithmicPhaseBProcessScale t := by
  have hcases :=
    Complex.logarithmicPhasePoissonBProcessInteriorModes_empty_or_nonempty
      t (a : ℤ) (b : ℤ)
  match hcases with
  | Or.inl hempty =>
      have hzero :=
        Complex.logarithmicPhaseBProcessInteriorBudget_eq_zero_of_empty
          t (a : ℤ) (b : ℤ) hempty
      have hnonneg :
          0 ≤ 68 * Complex.logarithmicPhaseBProcessScale t :=
        mul_nonneg (Nat.cast_nonneg 68)
          (Complex.logarithmicPhaseBProcessScale_nonneg t)
      exact Eq.subst
        (motive := fun value : ℝ =>
          value ≤ 68 * Complex.logarithmicPhaseBProcessScale t)
        hzero.symm hnonneg
  | Or.inr hnonempty =>
      have hclosed :=
        Complex.logarithmicPhaseBProcessInteriorBudget_le_closedMajorant
          t ht (a : ℤ) (b : ℤ)
          (Int.ofNat_le.mpr
            (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
          (Int.ofNat_zero_le b)
      have hsixtySeven :=
        Complex.logarithmicPhaseBProcessClosedInteriorMajorant_le_sixty_seven_scale_of_nonempty
          ht hgeometry hnonempty
      have hweaken :=
        Real.sixty_seven_mul_le_sixty_eight_mul
          (Complex.logarithmicPhaseBProcessScale_nonneg t)
      exact le_trans hclosed (le_trans hsixtySeven hweaken)

end

end LFunctions
end Boundary
