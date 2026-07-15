import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFarNegativeTailArithmetic

/-!
# Square-root transport for the curvature-square coefficient

The long-block inequality places the square-root scale below the support
length.  The sharp support-length ratio then places that scale below a fixed
multiple of the left endpoint.  Four powers of this comparison absorb the
four left-endpoint denominators in the curvature-square coefficient.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.square_le_fourth_of_square_le
    {T S : ℝ}
    (hT : 0 ≤ T)
    (hTS : T ≤ S ^ 2) :
    T ^ 2 ≤ S ^ 4 := by
  have hsquare := Real.square_le_square_of_nonneg hT hTS
  have hpower : (S ^ 2) ^ 2 = S ^ 4 := (pow_mul S 2 2).symm
  exact le_trans hsquare (le_of_eq hpower)

theorem Real.cube_scale_le_cube_left
    {S s left : ℝ}
    (hS : 0 ≤ S) (hs : 0 ≤ s)
    (hleft : 0 < left)
    (hscale : S ≤ s * left) :
    S ^ 3 ≤ s ^ 3 * left ^ 3 := by
  exact Real.ratio_cube_bound hleft hs hscale hS

theorem Real.length_mul_square_div_fourth_le_scale
    {T S length left s : ℝ}
    (hT : 0 ≤ T)
    (hS : 0 < S)
    (hlength : 0 ≤ length)
    (hleft : 0 < left)
    (hs : 0 ≤ s)
    (hTScale : T ≤ S ^ 2)
    (hlengthLeft : length ≤ s * left)
    (hscaleLeft : S ≤ s * left) :
    length * (T / left ^ 2) ^ 2 ≤ s ^ 4 * S := by
  have hTSquare := Real.square_le_fourth_of_square_le
    hT hTScale
  have hscaleCube := Real.cube_scale_le_cube_left
    hS.le hs hleft hscaleLeft
  have hleftFourthPos : 0 < left ^ 4 := pow_pos hleft 4
  have hlengthTimesSquare : length * T ^ 2 ≤ length * S ^ 4 :=
    mul_le_mul_of_nonneg_left hTSquare hlength
  have hlengthTimesFourth : length * S ^ 4 ≤ (s * left) * S ^ 4 :=
    mul_le_mul_of_nonneg_right hlengthLeft (pow_nonneg hS.le 4)
  have hlengthPower : length * T ^ 2 ≤ (s * left) * S ^ 4 :=
    le_trans hlengthTimesSquare hlengthTimesFourth
  have hleftNormalize :
      length * (T / left ^ 2) ^ 2 =
        (length * T ^ 2) / left ^ 4 := by
    have hdivPower : (T / left ^ 2) ^ 2 =
        T ^ 2 / (left ^ 2) ^ 2 := div_pow T (left ^ 2) 2
    have hdenominator : (left ^ 2) ^ 2 = left ^ 4 :=
      (pow_mul left 2 2).symm
    exact Eq.trans
      (congrArg (fun value : ℝ => length * value) hdivPower)
      (Eq.trans
        (mul_div_assoc length (T ^ 2) ((left ^ 2) ^ 2)).symm
        (congrArg (fun denominator : ℝ =>
          (length * T ^ 2) / denominator) hdenominator))
  have hsourceNormalize :
      (s * left) * S ^ 4 = (s * S * left) * S ^ 3 := by
    have hSFourth : S ^ 4 = S * S ^ 3 := pow_succ' S 3
    have hcoefficient : (s * left) * S = s * S * left := by
      exact Eq.trans (mul_assoc s left S)
        (Eq.trans
          (congrArg (fun value : ℝ => s * value) (mul_comm left S))
          (mul_assoc s S left).symm)
    exact Eq.trans
      (congrArg (fun value : ℝ => (s * left) * value) hSFourth)
      (Eq.trans (mul_assoc (s * left) S (S ^ 3)).symm
        (congrArg (fun value : ℝ => value * S ^ 3) hcoefficient))
  have hfactorNonneg : 0 ≤ s * S * left :=
    mul_nonneg (mul_nonneg hs hS.le) hleft.le
  have hscaledCube :=
    mul_le_mul_of_nonneg_left hscaleCube hfactorNonneg
  have hsTimesPower : s * S * s ^ 3 = s ^ 4 * S := by
    have hsFourth : s ^ 4 = s * s ^ 3 := pow_succ' s 3
    exact Eq.trans (mul_assoc s S (s ^ 3))
      (Eq.trans
        (congrArg (fun value : ℝ => s * value) (mul_comm S (s ^ 3)))
        (Eq.trans (mul_assoc s (s ^ 3) S).symm
          (congrArg (fun value : ℝ => value * S) hsFourth.symm)))
  have htargetNormalize :
      (s * S * left) * (s ^ 3 * left ^ 3) =
        (s ^ 4 * S) * left ^ 4 := by
    have hleftFourth : left ^ 4 = left * left ^ 3 := pow_succ' left 3
    have hfirst :
        (s * S * left) * (s ^ 3 * left ^ 3) =
          ((s * S * left) * s ^ 3) * left ^ 3 :=
      (mul_assoc (s * S * left) (s ^ 3) (left ^ 3)).symm
    have hcoefficient :
        (s * S * left) * s ^ 3 = (s ^ 4 * S) * left := by
      exact Eq.trans (mul_assoc (s * S) left (s ^ 3))
        (Eq.trans
          (congrArg (fun value : ℝ => (s * S) * value)
            (mul_comm left (s ^ 3)))
          (Eq.trans (mul_assoc (s * S) (s ^ 3) left).symm
            (congrArg (fun value : ℝ => value * left) hsTimesPower)))
    exact Eq.trans hfirst
      (Eq.trans
        (congrArg (fun value : ℝ => value * left ^ 3) hcoefficient)
        (Eq.trans (mul_assoc (s ^ 4 * S) left (left ^ 3))
          (congrArg (fun value : ℝ => (s ^ 4 * S) * value)
            hleftFourth.symm)))
  have hpowerCross :
      (s * left) * S ^ 4 ≤ (s ^ 4 * S) * left ^ 4 :=
    le_trans (le_of_eq hsourceNormalize)
      (le_trans hscaledCube (le_of_eq htargetNormalize))
  have hnumerator :
      length * T ^ 2 ≤ (s ^ 4 * S) * left ^ 4 :=
    le_trans hlengthPower hpowerCross
  have hdivide : (length * T ^ 2) / left ^ 4 ≤ s ^ 4 * S :=
    (div_le_iff₀ hleftFourthPos).mpr hnumerator
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ s ^ 4 * S)
    hleftNormalize.symm hdivide

theorem Real.norm_le_square_sqrt_one_add_norm
    (t : ℝ) :
    ‖t‖ ≤ (Real.sqrt (1 + ‖t‖)) ^ 2 := by
  have hinside : 0 ≤ 1 + ‖t‖ :=
    add_nonneg zero_le_one (norm_nonneg t)
  have hsquare := Real.sq_sqrt hinside
  exact le_trans (le_add_of_nonneg_left zero_le_one)
    (le_of_eq hsquare.symm)

theorem Complex.logarithmicPhase_length_curvatureSquare_le_sqrtScale
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) *
        (Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ))) ^ 2 ≤
      (7 / 4 : ℝ) ^ 4 * Real.sqrt (1 + ‖t‖) := by
  let S := Real.sqrt (1 + ‖t‖)
  let length :=
    Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ)
  let left :=
    Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ)
  have hSPos : 0 < S := by
    have hinside : 0 < 1 + ‖t‖ :=
      add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg t)
    exact Real.sqrt_pos.mpr hinside
  have hlength : 0 ≤ length :=
    Complex.logarithmicPhaseQuantitativeSupportLength_nonneg
      (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_order hgeometry))
  have hleft : 0 < left :=
    Complex.quantitativeSupportLeft_pos_of_two_le a
      (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry)
  have hlengthLeft : length ≤ (7 / 4 : ℝ) * left :=
    (Complex.longGeometry_sharp_support_ratios hgeometry).2
  have hscaleLeft : S ≤ (7 / 4 : ℝ) * left :=
    le_trans
      (Real.logarithmicPhaseLongBranchGeometry_sqrt hgeometry).le
      (Complex.longGeometry_canonicalLength_le_seven_fourths_left
        hgeometry)
  have htransport := Real.length_mul_square_div_fourth_le_scale
    (norm_nonneg t) hSPos hlength hleft
    (div_nonneg (Nat.cast_nonneg 7) (Nat.cast_nonneg 4))
    (Real.norm_le_square_sqrt_one_add_norm t)
    hlengthLeft hscaleLeft
  unfold Complex.logarithmicPhaseAdaptedCurvatureUpper
  exact htransport

theorem Complex.logarithmicPhase_curvatureFourthCoefficient_le_sqrtScale
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient
        t (a : ℤ) (b : ℤ) ≤
      3 * (7 / 4 : ℝ) ^ 4 * Real.sqrt (1 + ‖t‖) := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient
  have hbase :=
    Complex.logarithmicPhase_length_curvatureSquare_le_sqrtScale
      t a b hgeometry
  have hscaled :=
    mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg 3)
  have hleft :
      3 * Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) *
          (Complex.logarithmicPhaseAdaptedCurvatureUpper t
            (Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ))) ^ 2 =
        3 *
          (Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) *
            (Complex.logarithmicPhaseAdaptedCurvatureUpper t
              (Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ))) ^ 2) :=
    mul_assoc 3
      (Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ))
      ((Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ))) ^ 2)
  have hright :
      3 * ((7 / 4 : ℝ) ^ 4 * Real.sqrt (1 + ‖t‖)) =
        3 * (7 / 4 : ℝ) ^ 4 * Real.sqrt (1 + ‖t‖) :=
    (mul_assoc 3 ((7 / 4 : ℝ) ^ 4) (Real.sqrt (1 + ‖t‖))).symm
  exact le_trans (le_of_eq hleft)
    (le_trans hscaled (le_of_eq hright))

end
end LFunctions
end Boundary
