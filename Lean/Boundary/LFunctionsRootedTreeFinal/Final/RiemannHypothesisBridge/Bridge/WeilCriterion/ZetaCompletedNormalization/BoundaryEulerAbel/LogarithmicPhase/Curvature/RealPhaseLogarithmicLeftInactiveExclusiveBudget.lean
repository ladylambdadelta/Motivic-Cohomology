import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicExactActiveClosure

/-!
# Exclusive left-inactive and split zero-mode budgets

The complete left-inactive family has cardinality one, so its near and far
subclasses are mutually exclusive at the budget level.  The zero mode is
retained as a constant/square-root contribution plus endpoint quotients.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem two_thirds_add_two_thirds_eq_four_thirds :
    (2 / 3 : ℝ) + 2 / 3 = 4 / 3 :=
  Eq.trans (div_add_div_same 2 2 3)
    (congrArg (fun numerator : ℝ => numerator / 3)
      (realOfNat_add_eq_of_nat_eq 2 2 4 rfl))

private theorem four_thirds_le_thirteen_sixths :
    (4 / 3 : ℝ) ≤ 13 / 6 := by
  have hthree : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hsix : (6 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 5))
  have hfourMulSix : (4 : ℝ) * 6 = 24 :=
    realOfNat_mul_eq_of_nat_eq 4 6 24 rfl
  have heightMulThree : (8 : ℝ) * 3 = 24 :=
    realOfNat_mul_eq_of_nat_eq 8 3 24 rfl
  have hfraction : (4 / 3 : ℝ) = 8 / 6 :=
    (div_eq_div_iff hthree hsix).mpr
      (hfourMulSix.trans heightMulThree.symm)
  have hnat : (8 : ℕ) ≤ 13 :=
    Eq.subst (motive := fun value : ℕ => 8 ≤ value)
      (show 8 + 5 = 13 from rfl)
      (Nat.le_add_right 8 5)
  have hsameDenominator : (8 / 6 : ℝ) ≤ 13 / 6 :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hnat)
      (Nat.cast_nonneg 6)
  exact Eq.subst (motive := fun value : ℝ => value ≤ 13 / 6)
    hfraction.symm hsameDenominator

def Complex.logarithmicPhaseFiniteLeftSharpBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget t a b +
    Complex.logarithmicPhaseFiniteLeftFarCrossingBudget t a b +
      Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget t a b

def Real.logarithmicPhaseEndpointComponent
    (t : ℝ) (b : ℕ) : ℝ :=
  ((b + 1 : ℕ) : ℝ) / ‖t‖

def Real.logarithmicPhaseSquareRootComponent
    (t : ℝ) : ℝ :=
  Real.sqrt (1 + ‖t‖)

theorem Complex.logarithmicPhaseFiniteLeftNear_union_far_card_le_one
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhaseFiniteLeftNearEndpointModes
        t (a : ℤ) (b : ℤ) ∪
      Complex.logarithmicPhaseFiniteLeftFarModes
        t (a : ℤ) (b : ℤ)).card ≤ 1 := by
  have hunion := Complex.logarithmicPhaseFiniteLeftNear_union_far
    t (a : ℤ) (b : ℤ)
  have hcard := Complex.logarithmicPhasePoissonLeftInactive_card_le_one
    t ht (a : ℤ) (b : ℤ)
    (Int.ofNat_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_order hgeometry))
  exact Eq.subst (motive := fun modes : Finset ℤ => modes.card ≤ 1)
    hunion.symm hcard

theorem Complex.logarithmicPhaseFiniteLeftNearFar_not_both_nonempty
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhaseFiniteLeftNearEndpointModes
        t (a : ℤ) (b : ℤ) = ∅) ∨
      (Complex.logarithmicPhaseFiniteLeftFarModes
        t (a : ℤ) (b : ℤ) = ∅) := by
  match
    (Complex.logarithmicPhaseFiniteLeftNearEndpointModes
      t (a : ℤ) (b : ℤ)).eq_empty_or_nonempty with
  | Or.inl hnearEmpty => exact Or.inl hnearEmpty
  | Or.inr hnearNonempty =>
      match hnearNonempty with
      | ⟨m, hm⟩ =>
          have hdisjoint : Disjoint
              (Complex.logarithmicPhaseFiniteLeftNearEndpointModes
                t (a : ℤ) (b : ℤ))
              (Complex.logarithmicPhaseFiniteLeftFarModes
                t (a : ℤ) (b : ℤ)) :=
            Finset.disjoint_left.mpr (fun q hnear hfar =>
              have hnData :=
                (Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
                  t (a : ℤ) (b : ℤ) q).mp hnear
              have hfData :=
                (Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff
                  t (a : ℤ) (b : ℤ) q).mp hfar
              (not_lt_of_ge hnData.2) hfData.2)
          exact Or.inr
            (Finset.eq_empty_iff_forall_not_mem.mpr (fun n hn =>
              have hcard :=
                Complex.logarithmicPhaseFiniteLeftNear_union_far_card_le_one
                  t ht a b hgeometry
              have hmUnion := Finset.mem_union_left
                (Complex.logarithmicPhaseFiniteLeftFarModes
                  t (a : ℤ) (b : ℤ)) hm
              have hnUnion := Finset.mem_union_right
                (Complex.logarithmicPhaseFiniteLeftNearEndpointModes
                  t (a : ℤ) (b : ℤ)) hn
              have heq : m = n :=
                (Finset.card_le_one.mp hcard) m hmUnion n hnUnion
              (Finset.disjoint_left.mp hdisjoint) (heq ▸ hm) hn))

theorem Complex.logarithmicPhaseFiniteLeftNearBudget_eq_zero_of_empty
    (t : ℝ) (a b : ℤ)
    (hempty : Complex.logarithmicPhaseFiniteLeftNearEndpointModes
      t a b = ∅) :
    Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget t a b = 0 := by
  unfold Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
  exact Eq.trans
    (congrArg
      (fun modes : Finset ℤ =>
        ∑ m ∈ modes,
          Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
            t a b m)
      hempty)
    Finset.sum_empty

theorem Complex.logarithmicPhaseFiniteLeftFarCrossingBudget_eq_zero_of_empty
    (t : ℝ) (a b : ℤ)
    (hempty : Complex.logarithmicPhaseFiniteLeftFarModes t a b = ∅) :
    Complex.logarithmicPhaseFiniteLeftFarCrossingBudget t a b = 0 := by
  unfold Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
  exact Eq.trans
    (congrArg (fun modes : Finset ℤ => ∑ _m ∈ modes, (2 / 3 : ℝ)) hempty)
    Finset.sum_empty

theorem Complex.logarithmicPhaseFiniteLeftSharpBudget_le_thirteen_sixths_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteLeftSharpBudget
        t (a : ℤ) (b : ℤ) ≤
      (13 / 6 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  match
    Complex.logarithmicPhaseFiniteLeftNearFar_not_both_nonempty
      t ht a b hgeometry with
  | Or.inl hnearEmpty =>
      have hnearZero :=
        Complex.logarithmicPhaseFiniteLeftNearBudget_eq_zero_of_empty
          t (a : ℤ) (b : ℤ) hnearEmpty
      have hcross :=
        Complex.logarithmicPhaseFiniteLeftFarCrossingBudget_le_two_thirds_scale
          t ht a b hgeometry
      have hreciprocal :=
        Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget_le_two_thirds_scale
          t ht a b hgeometry
      have hsum := add_le_add hcross hreciprocal
      have hcoefficient : (4 / 3 : ℝ) ≤ 13 / 6 :=
        four_thirds_le_thirteen_sixths
      have henlarge := mul_le_mul_of_nonneg_right hcoefficient
        (Complex.logarithmicPhaseBProcessScale_nonneg t)
      have hsumNormalize :
          (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t +
              (2 / 3) * Complex.logarithmicPhaseBProcessScale t =
            (4 / 3) * Complex.logarithmicPhaseBProcessScale t :=
        Eq.trans
          (add_mul (2 / 3 : ℝ) (2 / 3)
            (Complex.logarithmicPhaseBProcessScale t)).symm
          (congrArg
            (fun coefficient : ℝ => coefficient *
              Complex.logarithmicPhaseBProcessScale t)
            two_thirds_add_two_thirds_eq_four_thirds)
      have htailBound := le_trans hsum
        (le_trans (le_of_eq hsumNormalize) henlarge)
      have hzeroForm :
          0 + Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
                t (a : ℤ) (b : ℤ) +
              Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
                t (a : ℤ) (b : ℤ) =
            Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
                t (a : ℤ) (b : ℤ) +
              Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
                t (a : ℤ) (b : ℤ) :=
        congrArg
          (fun value : ℝ => value +
            Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
              t (a : ℤ) (b : ℤ))
          (zero_add
            (Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
              t (a : ℤ) (b : ℤ)))
      unfold Complex.logarithmicPhaseFiniteLeftSharpBudget
      exact Eq.subst (motive := fun value : ℝ => value + _ + _ ≤ _)
        hnearZero.symm
        (Eq.subst (motive := fun value : ℝ => value ≤ _)
          hzeroForm.symm htailBound)
  | Or.inr hfarEmpty =>
      have hcrossZero :=
        Complex.logarithmicPhaseFiniteLeftFarCrossingBudget_eq_zero_of_empty
          t (a : ℤ) (b : ℤ) hfarEmpty
      have hreciprocalZero :=
        Complex.logarithmicPhaseFiniteLeftFarBudget_eq_zero_of_empty
          t (a : ℤ) (b : ℤ) hfarEmpty
      have hnear :=
        Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget_le_thirteen_sixths_scale
          ht ht_nonneg hgeometry
      have hsharpToNear :
          Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
                t (a : ℤ) (b : ℤ) +
              Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
                t (a : ℤ) (b : ℤ) +
              Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
                t (a : ℤ) (b : ℤ) =
            Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
              t (a : ℤ) (b : ℤ) := by
        exact Eq.trans
          (congrArg
            (fun value : ℝ =>
              Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
                  t (a : ℤ) (b : ℤ) + value +
                Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
                  t (a : ℤ) (b : ℤ))
            hcrossZero)
          (Eq.trans
            (congrArg
              (fun value : ℝ =>
                Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
                    t (a : ℤ) (b : ℤ) + 0 + value)
              hreciprocalZero)
            (Eq.trans
              (add_zero
                (Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
                    t (a : ℤ) (b : ℤ) + 0))
              (add_zero
                (Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
                  t (a : ℤ) (b : ℤ)))))
      unfold Complex.logarithmicPhaseFiniteLeftSharpBudget
      exact Eq.subst (motive := fun value : ℝ => value ≤ _)
        hsharpToNear.symm hnear

theorem Real.zeroMode_endpoint_squareRoot_split
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ) (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeZeroModeBudget
        t (a : ℤ) (b : ℤ) ≤
      3 * Real.logarithmicPhaseEndpointComponent t b +
        (2 / 3 : ℝ) * Real.logarithmicPhaseSquareRootComponent t := by
  let E := Real.logarithmicPhaseEndpointComponent t b
  let S := Real.logarithmicPhaseSquareRootComponent t
  have hnormPos := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hbNumerator : (b : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by
    have hnat : b ≤ b + 1 := Nat.le_add_right b 1
    exact Nat.cast_le.mpr hnat
  have hrightRaw : (b : ℝ) / ‖t‖ ≤ ((b + 1 : ℕ) : ℝ) / ‖t‖ :=
    div_le_div_of_nonneg_right hbNumerator hnormPos.le
  have hright : (b : ℝ) / ‖t‖ ≤ E := by
    unfold E Real.logarithmicPhaseEndpointComponent
    exact hrightRaw
  have haNonneg : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hlengthNumerator : (b : ℝ) - (a : ℝ) ≤ ((b + 1 : ℕ) : ℝ) :=
    le_trans (sub_le_self (b : ℝ) haNonneg) hbNumerator
  have hlengthRaw :
      ((b : ℝ) - (a : ℝ)) / ‖t‖ ≤ ((b + 1 : ℕ) : ℝ) / ‖t‖ :=
    div_le_div_of_nonneg_right hlengthNumerator hnormPos.le
  have hlength : ((b : ℝ) - (a : ℝ)) / ‖t‖ ≤ E := by
    unfold E Real.logarithmicPhaseEndpointComponent
    exact hlengthRaw
  have hsqrtOne : (1 : ℝ) ≤ S := by
    unfold S Real.logarithmicPhaseSquareRootComponent
    exact Real.logarithmicPhase_one_le_sqrt_one_add_norm t ht
  have htwoThirdNonneg : (0 : ℝ) ≤ 2 / 3 :=
    div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)
  have hconstantScaled : (2 / 3 : ℝ) * 1 ≤ (2 / 3) * S :=
    mul_le_mul_of_nonneg_left hsqrtOne htwoThirdNonneg
  have hconstant : (2 / 3 : ℝ) ≤ (2 / 3) * S := by
    calc
      (2 / 3 : ℝ) = (2 / 3 : ℝ) * 1 := (mul_one _).symm
      _ ≤ (2 / 3 : ℝ) * S := hconstantScaled
  have hrightTwice : 2 * ((b : ℝ) / ‖t‖) ≤ 2 * E :=
    mul_le_mul_of_nonneg_left hright (Nat.cast_nonneg 2)
  have hlengthCast :
      ((b : ℤ) : ℝ) - ((a : ℤ) : ℝ) = (b : ℝ) - (a : ℝ) :=
    congrArg₂ (fun left right : ℝ => left - right)
      (show ((b : ℤ) : ℝ) = (b : ℝ) from rfl)
      (show ((a : ℤ) : ℝ) = (a : ℝ) from rfl)
  have hsmulIdentity :
      ((((b : ℤ) : ℝ) - ((a : ℤ) : ℝ) : ℝ) • ‖t‖⁻¹) =
        ((b : ℝ) - (a : ℝ)) / ‖t‖ := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value • ‖t‖⁻¹) hlengthCast)
      (Real.natBlockLength_smul_normInv_eq_div t a b)
  have hsmul :
      ((((b : ℤ) : ℝ) - ((a : ℤ) : ℝ) : ℝ) • ‖t‖⁻¹) ≤ E :=
    Eq.subst (motive := fun value : ℝ => value ≤ E)
      hsmulIdentity.symm hlength
  have hbudgetPieces :
      (2 / 3 : ℝ) + 2 * ((b : ℝ) / ‖t‖) +
          ((((b : ℤ) : ℝ) - ((a : ℤ) : ℝ) : ℝ) • ‖t‖⁻¹) ≤
        (2 / 3) * S + 2 * E + E :=
    add_le_add (add_le_add hconstant hrightTwice) hsmul
  have hrightCast : ((b : ℤ) : ℝ) = (b : ℝ) := rfl
  have hbudgetForm :
      Complex.logarithmicPhaseQuantitativeZeroModeBudget
          t (a : ℤ) (b : ℤ) =
        (2 / 3 : ℝ) + 2 * ((b : ℝ) / ‖t‖) +
          ((((b : ℤ) : ℝ) - ((a : ℤ) : ℝ) : ℝ) • ‖t‖⁻¹) := by
    unfold Complex.logarithmicPhaseQuantitativeZeroModeBudget
    exact congrArg
      (fun right : ℝ =>
        (2 / 3 : ℝ) + 2 * (right / ‖t‖) +
          ((((b : ℤ) : ℝ) - ((a : ℤ) : ℝ) : ℝ) • ‖t‖⁻¹))
      hrightCast
  have hendpointCollect : 2 * E + E = 3 * E := by
    exact Eq.trans
      (congrArg (fun value : ℝ => 2 * E + value) (one_mul E).symm)
      (Eq.trans (add_mul 2 1 E).symm
        (congrArg (fun coefficient : ℝ => coefficient * E)
          Real.two_add_one_eq_three))
  have hreorder :
      (2 / 3 : ℝ) * S + 2 * E + E =
        3 * E + (2 / 3) * S := by
    exact Eq.trans
      (add_assoc ((2 / 3 : ℝ) * S) (2 * E) E)
      (Eq.trans
        (congrArg (fun value : ℝ => (2 / 3) * S + value) hendpointCollect)
        (add_comm ((2 / 3 : ℝ) * S) (3 * E)))
  exact Eq.subst
    (motive := fun left : ℝ => left ≤ 3 * E + (2 / 3) * S)
    hbudgetForm.symm
    (le_trans hbudgetPieces (le_of_eq hreorder))

end

end LFunctions
end Boundary
