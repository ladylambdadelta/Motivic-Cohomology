import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessDistributedArithmetic

/-!
# Termwise bounds for the distributed B-process budget

This file bounds the four products contributed by the additive cardinality
term and provides the final eight-product assembly lemma.  The frequency-term
products are stated in their cancellation-ready form and are discharged in the
next owner from dyadic comparability and positivity of `‖t‖`.
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

private theorem real_eight_add_one_eq_nine :
    (8 : ℝ) + 1 = 9 := by
  have height : ((8 : ℕ) : ℝ) = 8 := Nat.cast_ofNat
  have hone : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
  have hnine : ((9 : ℕ) : ℝ) = 9 := Nat.cast_ofNat
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left + right)
      height.symm hone.symm)
    (Eq.trans (realOfNat_add_eq_of_nat_eq 8 1 9 rfl) hnine)

private theorem real_two_mul_two_eq_four :
    (2 : ℝ) * 2 = 4 :=
  Eq.trans (two_mul (2 : ℝ)) two_add_two_eq_four

private theorem real_four_mul_four_eq_sixteen :
    (4 : ℝ) * 4 = 16 := by
  have hfour : ((4 : ℕ) : ℝ) = 4 := Nat.cast_ofNat
  have hsixteen : ((16 : ℕ) : ℝ) = 16 := Nat.cast_ofNat
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left * right)
      hfour.symm hfour.symm)
    (Eq.trans (realOfNat_mul_eq_of_nat_eq 4 4 16 rfl) hsixteen)

private theorem real_four_mul_two_eq_eight :
    (4 : ℝ) * 2 = 8 := by
  have hfour : ((4 : ℕ) : ℝ) = 4 := Nat.cast_ofNat
  have htwo : ((2 : ℕ) : ℝ) = 2 := Nat.cast_ofNat
  have height : ((8 : ℕ) : ℝ) = 8 := Nat.cast_ofNat
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left * right)
      hfour.symm htwo.symm)
    (Eq.trans (realOfNat_mul_eq_of_nat_eq 4 2 8 rfl) height)

def Complex.logarithmicPhaseBProcessCrossingScalar : ℝ :=
  4 / 3

def Complex.logarithmicPhaseBProcessTailScalar
    (t : ℝ) (b : ℤ) : ℝ :=
  2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖)

def Complex.logarithmicPhaseBProcessCentralScalar
    (t : ℝ) (b : ℤ) : ℝ :=
  2 * ((b : ℝ) / Complex.logarithmicPhaseBProcessScale t)

def Complex.logarithmicPhaseBProcessFrequencyCardScalar
    (t : ℝ) (a : ℤ) : ℝ :=
  ‖t‖ /
    (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a)

theorem Complex.logarithmicPhaseBProcessPerModeEndpointMajorant_eq_scalars
    (t : ℝ) (b : ℤ) :
    Complex.logarithmicPhaseBProcessPerModeEndpointMajorant t b =
      Complex.logarithmicPhaseBProcessCrossingScalar +
        Complex.logarithmicPhaseBProcessTailScalar t b +
        Complex.logarithmicPhaseBProcessCentralScalar t b +
        Complex.logarithmicPhaseBProcessTailScalar t b := by
  rfl

theorem Complex.logarithmicPhaseModeRangeCardMajorant_eq_two_add_frequencyScalar
    (t : ℝ) (a : ℤ) :
    Complex.logarithmicPhaseModeRangeCardMajorant t a =
      2 + Complex.logarithmicPhaseBProcessFrequencyCardScalar t a := by
  rfl

theorem Complex.logarithmicPhaseBProcessClosedInteriorMajorant_eq_eight_products
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseBProcessClosedInteriorMajorant t a b =
      (2 * Complex.logarithmicPhaseBProcessCrossingScalar +
        2 * Complex.logarithmicPhaseBProcessTailScalar t b +
        2 * Complex.logarithmicPhaseBProcessCentralScalar t b +
        2 * Complex.logarithmicPhaseBProcessTailScalar t b) +
      (Complex.logarithmicPhaseBProcessFrequencyCardScalar t a *
          Complex.logarithmicPhaseBProcessCrossingScalar +
        Complex.logarithmicPhaseBProcessFrequencyCardScalar t a *
          Complex.logarithmicPhaseBProcessTailScalar t b +
        Complex.logarithmicPhaseBProcessFrequencyCardScalar t a *
          Complex.logarithmicPhaseBProcessCentralScalar t b +
        Complex.logarithmicPhaseBProcessFrequencyCardScalar t a *
          Complex.logarithmicPhaseBProcessTailScalar t b) := by
  unfold Complex.logarithmicPhaseBProcessClosedInteriorMajorant
  have hcard :=
    Complex.logarithmicPhaseModeRangeCardMajorant_eq_two_add_frequencyScalar
      t a
  have hpacket :=
    Complex.logarithmicPhaseBProcessPerModeEndpointMajorant_eq_scalars
      t b
  exact
    (congrArg₂ (fun left right : ℝ => left * right) hcard hpacket).trans
      (Real.add_mul_four_term_sum
        2 (Complex.logarithmicPhaseBProcessFrequencyCardScalar t a)
        Complex.logarithmicPhaseBProcessCrossingScalar
        (Complex.logarithmicPhaseBProcessTailScalar t b)
        (Complex.logarithmicPhaseBProcessCentralScalar t b)
        (Complex.logarithmicPhaseBProcessTailScalar t b))

theorem Complex.logarithmicPhaseBProcessCrossingScalar_nonneg :
    0 ≤ Complex.logarithmicPhaseBProcessCrossingScalar := by
  unfold Complex.logarithmicPhaseBProcessCrossingScalar
  exact div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 3)

theorem Complex.logarithmicPhaseBProcessTailScalar_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {b : ℤ} (hb : 0 ≤ b) :
    0 ≤ Complex.logarithmicPhaseBProcessTailScalar t b := by
  unfold Complex.logarithmicPhaseBProcessTailScalar
  exact mul_nonneg zero_le_two
    (Complex.logarithmicPhaseBProcess_endpoint_mul_scale_div_norm_nonneg
      t ht hb)

theorem Complex.logarithmicPhaseBProcessCentralScalar_nonneg
    (t : ℝ) {b : ℤ} (hb : 0 ≤ b) :
    0 ≤ Complex.logarithmicPhaseBProcessCentralScalar t b := by
  unfold Complex.logarithmicPhaseBProcessCentralScalar
  exact mul_nonneg zero_le_two
    (Complex.logarithmicPhaseBProcess_endpoint_div_scale_nonneg t hb)

theorem Complex.logarithmicPhaseBProcessFrequencyCardScalar_nonneg
    (t : ℝ) {a : ℤ} (ha : 1 ≤ a) :
    0 ≤ Complex.logarithmicPhaseBProcessFrequencyCardScalar t a := by
  unfold Complex.logarithmicPhaseBProcessFrequencyCardScalar
  have hleft := Complex.integerBlockCutoffSupportLeftEndpoint_pos ha
  have hdenominator := mul_pos Complex.two_mul_pi_pos hleft
  exact div_nonneg (norm_nonneg t) hdenominator.le

theorem Real.eight_thirds_le_three :
    (8 : ℝ) / 3 ≤ 3 := by
  have hthreePos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (Nat.succ_pos 2)
  have heightNine : (8 : ℝ) ≤ 9 := by
    calc
      (8 : ℝ) ≤ 8 + 1 := le_add_of_nonneg_right zero_le_one
      _ = 9 := real_eight_add_one_eq_nine
  have hthreeMulThree : (3 : ℝ) * 3 = 9 :=
    Eq.trans (Nat.cast_mul 3 3).symm
      (congrArg (fun value : ℕ => (value : ℝ))
        (show (3 : ℕ) * 3 = 9 from rfl))
  have hproductBound : (8 : ℝ) ≤ 3 * 3 :=
    Eq.subst
      (motive := fun value : ℝ => (8 : ℝ) ≤ value)
      hthreeMulThree.symm heightNine
  exact (div_le_iff₀ hthreePos).mpr
    hproductBound

theorem Complex.two_mul_crossingScalar_le_three_mul_scale
    (t : ℝ) :
    2 * Complex.logarithmicPhaseBProcessCrossingScalar ≤
      3 * Complex.logarithmicPhaseBProcessScale t := by
  have hcrossing :
      2 * Complex.logarithmicPhaseBProcessCrossingScalar = (8 : ℝ) / 3 := by
    unfold Complex.logarithmicPhaseBProcessCrossingScalar
    exact Eq.trans (mul_div_assoc 2 4 3).symm
      (congrArg (fun value : ℝ => value / 3)
        (realOfNat_mul_eq_of_nat_eq 2 4 8 rfl))
  have hthree := Real.eight_thirds_le_three
  have hscale := Complex.logarithmicPhaseBProcessScale_one_le t
  have hscaled := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg 3)
  have hthreeScaled :
      (3 : ℝ) ≤ 3 * Complex.logarithmicPhaseBProcessScale t :=
    le_trans (le_of_eq (mul_one (3 : ℝ)).symm) hscaled
  exact le_trans (le_of_eq hcrossing)
    (le_trans hthree hthreeScaled)

theorem Complex.two_mul_tailScalar_le_sixteen_mul_scale_of_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    2 * Complex.logarithmicPhaseBProcessTailScalar t (b : ℤ) ≤
      16 * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessTailScalar
  have hbase :=
    Real.longGeometry_blockRight_mul_scale_div_norm_le_four_mul_scale_of_nonempty
      ht hgeometry hnonempty
  have hscaled := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg 4)
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
      4 * (4 * Complex.logarithmicPhaseBProcessScale t) =
        16 * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans (mul_assoc 4 4 _).symm
      (congrArg
        (fun value : ℝ => value * Complex.logarithmicPhaseBProcessScale t)
        real_four_mul_four_eq_sixteen)
  exact le_trans (le_of_eq hleft)
    (le_trans hscaled (le_of_eq hright))

theorem Complex.two_mul_centralScalar_le_eight_mul_scale_of_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    2 * Complex.logarithmicPhaseBProcessCentralScalar t (b : ℤ) ≤
      8 * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessCentralScalar
  have hbase :=
    Real.longGeometry_blockRight_div_scale_le_two_mul_scale_of_nonempty
      ht hgeometry hnonempty
  have hscaled := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg 4)
  have hleft :
      2 * (2 * ((b : ℝ) /
        Complex.logarithmicPhaseBProcessScale t)) =
        4 * ((b : ℝ) /
          Complex.logarithmicPhaseBProcessScale t) := by
    exact Eq.trans (mul_assoc 2 2 _).symm
      (congrArg
        (fun value : ℝ => value *
          ((b : ℝ) / Complex.logarithmicPhaseBProcessScale t))
        real_two_mul_two_eq_four)
  have hright :
      4 * (2 * Complex.logarithmicPhaseBProcessScale t) =
        8 * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans (mul_assoc 4 2 _).symm
      (congrArg
        (fun value : ℝ => value * Complex.logarithmicPhaseBProcessScale t)
        real_four_mul_two_eq_eight)
  exact le_trans (le_of_eq hleft)
    (le_trans hscaled (le_of_eq hright))

/-- Eight explicit component inequalities close a distributed budget. -/
theorem Real.distributed_eight_products_le_sum
    {xC xL xM xR yC yL yM yR S : ℝ}
    (hxC : xC ≤ 3 * S)
    (hxL : xL ≤ 16 * S)
    (hxM : xM ≤ 8 * S)
    (hxR : xR ≤ 16 * S)
    (hyC : yC ≤ 4 * S)
    (hyL : yL ≤ 12 * S)
    (hyM : yM ≤ 12 * S)
    (hyR : yR ≤ 12 * S) :
    (xC + xL + xM + xR) + (yC + yL + yM + yR) ≤
      (3 * S + 16 * S + 8 * S + 16 * S) +
        (4 * S + 12 * S + 12 * S + 12 * S) := by
  exact Real.add_two_four_term_bounds
    hxC hxL hxM hxR hyC hyL hyM hyR

end

end LFunctions
end Boundary
