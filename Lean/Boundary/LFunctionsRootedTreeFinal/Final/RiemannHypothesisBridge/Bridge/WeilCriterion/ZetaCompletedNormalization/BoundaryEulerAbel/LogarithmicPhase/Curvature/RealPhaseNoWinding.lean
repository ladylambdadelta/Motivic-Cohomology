import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogGap

/-!
# No-winding bridge for reduced logarithmic increments

This file owns the local bridge from principal-interval control of raw
increments to reduced-increment monotonicity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A positive nonzero `2π` lattice point lies at least `π` away from every
angle in the principal interval. -/
theorem Real.principalAngle_posInt_twoPi_distance_ge_pi
    {θ : ℝ}
    (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi)
    (q : ℕ) :
    Real.pi ≤
      ‖θ - (2 * Real.pi * (((Nat.succ q : ℕ) : ℝ)))‖ := by
  let A : ℝ := 2 * Real.pi * (((Nat.succ q : ℕ) : ℝ))
  have hθ_right : θ ≤ Real.pi :=
    hθ.2
  have htwo_pi_nonneg : 0 ≤ 2 * Real.pi :=
    mul_nonneg zero_le_two Real.pi_nonneg
  have hsucc_one_nat : 1 ≤ Nat.succ q :=
    Nat.succ_le_succ (Nat.zero_le q)
  have hsucc_one : (1 : ℝ) ≤ (((Nat.succ q : ℕ) : ℝ)) :=
    Eq.subst
      (motive := fun r : ℝ => r ≤ (((Nat.succ q : ℕ) : ℝ)))
      Nat.cast_one
      (Nat.cast_le.mpr hsucc_one_nat)
  have htwo_pi_le_A : 2 * Real.pi ≤ A := by
    calc
      2 * Real.pi = 2 * Real.pi * 1 :=
        (mul_one (2 * Real.pi)).symm
      _ ≤ 2 * Real.pi * (((Nat.succ q : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsucc_one htwo_pi_nonneg
  have hpi_le_A_sub_theta : Real.pi ≤ A - θ := by
    have hsum : Real.pi + θ ≤ A := by
      have hpi_add_theta_le_two_pi : Real.pi + θ ≤ 2 * Real.pi := by
        calc
          Real.pi + θ ≤ Real.pi + Real.pi :=
              add_le_add_left hθ_right Real.pi
          _ = 2 * Real.pi :=
            (two_mul Real.pi).symm
      exact le_trans hpi_add_theta_le_two_pi htwo_pi_le_A
    calc
      Real.pi = Real.pi + θ - θ :=
        (add_sub_cancel_right Real.pi θ).symm
      _ ≤ A - θ :=
        sub_le_sub_right hsum θ
  have hneg_le_abs : A - θ ≤ ‖θ - A‖ := by
    have hnorm_abs : ‖θ - A‖ = |θ - A| :=
      Real.norm_eq_abs (θ - A)
    have hneg_abs : -(θ - A) ≤ |θ - A| :=
      neg_le_abs (θ - A)
    have hA_sub : A - θ = -(θ - A) :=
      (neg_sub θ A).symm
    exact
      Eq.subst
        (motive := fun r : ℝ => r ≤ ‖θ - A‖)
        hA_sub.symm
        (Eq.subst
          (motive := fun r : ℝ => -(θ - A) ≤ r)
          hnorm_abs.symm
          hneg_abs)
  exact le_trans hpi_le_A_sub_theta hneg_le_abs

/-- A negative nonzero `2π` lattice point lies at least `π` away from every
angle in the principal interval. -/
theorem Real.principalAngle_negInt_twoPi_distance_ge_pi
    {θ : ℝ}
    (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi)
    (q : ℕ) :
    Real.pi ≤
      ‖θ - (2 * Real.pi * (-(((Nat.succ q : ℕ) : ℝ))))‖ := by
  let A : ℝ := 2 * Real.pi * (((Nat.succ q : ℕ) : ℝ))
  have hθ_left : -Real.pi < θ :=
    hθ.1
  have htwo_pi_nonneg : 0 ≤ 2 * Real.pi :=
    mul_nonneg zero_le_two Real.pi_nonneg
  have hsucc_one_nat : 1 ≤ Nat.succ q :=
    Nat.succ_le_succ (Nat.zero_le q)
  have hsucc_one : (1 : ℝ) ≤ (((Nat.succ q : ℕ) : ℝ)) :=
    Eq.subst
      (motive := fun r : ℝ => r ≤ (((Nat.succ q : ℕ) : ℝ)))
      Nat.cast_one
      (Nat.cast_le.mpr hsucc_one_nat)
  have htwo_pi_le_A : 2 * Real.pi ≤ A := by
    calc
      2 * Real.pi = 2 * Real.pi * 1 :=
        (mul_one (2 * Real.pi)).symm
      _ ≤ 2 * Real.pi * (((Nat.succ q : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsucc_one htwo_pi_nonneg
  have hpi_lt_theta_add_A : Real.pi < θ + A := by
    have hpi_lt_theta_add_two_pi : Real.pi < θ + 2 * Real.pi := by
      calc
        Real.pi = -Real.pi + 2 * Real.pi := by
          calc
            Real.pi = 0 + Real.pi :=
              (zero_add Real.pi).symm
            _ = (-Real.pi + Real.pi) + Real.pi :=
              congrArg (fun r : ℝ => r + Real.pi) (neg_add_cancel Real.pi).symm
            _ = -Real.pi + (Real.pi + Real.pi) :=
              add_assoc (-Real.pi) Real.pi Real.pi
            _ = -Real.pi + 2 * Real.pi :=
              congrArg (fun r : ℝ => -Real.pi + r) (two_mul Real.pi).symm
        _ < θ + 2 * Real.pi :=
          add_lt_add_right hθ_left (2 * Real.pi)
    exact lt_of_lt_of_le hpi_lt_theta_add_two_pi
      (add_le_add_left htwo_pi_le_A θ)
  have hpi_le_theta_add_A : Real.pi ≤ θ + A :=
    le_of_lt hpi_lt_theta_add_A
  have hcenter :
      2 * Real.pi * (-(((Nat.succ q : ℕ) : ℝ))) = -A :=
    mul_neg (2 * Real.pi) (((Nat.succ q : ℕ) : ℝ))
  have hdiff :
      θ - (2 * Real.pi * (-(((Nat.succ q : ℕ) : ℝ)))) = θ + A := by
    calc
      θ - (2 * Real.pi * (-(((Nat.succ q : ℕ) : ℝ)))) =
          θ - (-A) :=
        congrArg (fun r : ℝ => θ - r) hcenter
      _ = θ + A :=
        sub_neg_eq_add θ A
  have hle_abs : θ + A ≤ ‖θ + A‖ := by
    have hnorm_abs : ‖θ + A‖ = |θ + A| :=
      Real.norm_eq_abs (θ + A)
    exact
      Eq.subst
        (motive := fun r : ℝ => θ + A ≤ r)
        hnorm_abs.symm
        (le_abs_self (θ + A))
  exact
    Eq.subst
      (motive := fun r : ℝ => Real.pi ≤ ‖r‖)
      hdiff.symm
      (le_trans hpi_le_theta_add_A hle_abs)

/-- Inside the principal interval, the zero `2πℤ` lattice point is a closest
lattice point. -/
theorem Real.principalAngle_zero_twoPi_distance_le_intDistance
    {θ : ℝ}
    (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi)
    (k : ℤ) :
    ‖θ - (2 * Real.pi * (0 : ℝ))‖ ≤
      ‖θ - (2 * Real.pi * (k : ℝ))‖ := by
  have hθ_abs_le_pi : ‖θ - (2 * Real.pi * (0 : ℝ))‖ ≤ Real.pi := by
    have hzero_mul : 2 * Real.pi * (0 : ℝ) = 0 :=
      mul_zero (2 * Real.pi)
    have hdiff_zero : θ - (2 * Real.pi * (0 : ℝ)) = θ := by
      exact congrArg (fun r : ℝ => θ - r) hzero_mul
        |>.trans (sub_zero θ)
    have hθ_abs : |θ| ≤ Real.pi :=
      abs_le.mpr (And.intro (le_of_lt hθ.1) hθ.2)
    have hθ_norm : ‖θ‖ = |θ| :=
      Real.norm_eq_abs θ
    exact
      Eq.subst
        (motive := fun r : ℝ => r ≤ Real.pi)
        (congrArg norm hdiff_zero).symm
        (Eq.subst
          (motive := fun r : ℝ => r ≤ Real.pi)
          hθ_norm.symm
          hθ_abs)
  match k with
  | Int.ofNat n =>
      match n with
      | Nat.zero =>
          exact
            Eq.subst
              (motive := fun r : ℝ =>
                ‖θ - (2 * Real.pi * (0 : ℝ))‖ ≤
                  ‖θ - (2 * Real.pi * r)‖)
              (Int.cast_zero.symm)
              le_rfl
      | Nat.succ q =>
          exact le_trans hθ_abs_le_pi
            (Real.principalAngle_posInt_twoPi_distance_ge_pi hθ q)
  | Int.negSucc q =>
      have hcast_neg :
          (((Int.negSucc q : ℤ) : ℝ)) =
            -(((Nat.succ q : ℕ) : ℝ)) :=
        Int.cast_negSucc q
      exact
        Eq.subst
          (motive := fun r : ℝ =>
            ‖θ - (2 * Real.pi * (0 : ℝ))‖ ≤
              ‖θ - (2 * Real.pi * r)‖)
          hcast_neg.symm
          (le_trans hθ_abs_le_pi
            (Real.principalAngle_negInt_twoPi_distance_ge_pi hθ q))

/-- The periodic principal interval `(-π, -π + 2π]` has the same zero-lattice
closest-point property as `(-π, π]`. -/
theorem Real.periodicPrincipalAngle_zero_twoPi_distance_le_intDistance
    {θ : ℝ}
    (hθ : θ ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
    (k : ℤ) :
    ‖θ - (2 * Real.pi * (0 : ℝ))‖ ≤
      ‖θ - (2 * Real.pi * (k : ℝ))‖ := by
  have hupper : -Real.pi + (2 * Real.pi) = Real.pi := by
    calc
      -Real.pi + (2 * Real.pi) = -Real.pi + (Real.pi + Real.pi) :=
        congrArg (fun r : ℝ => -Real.pi + r) (two_mul Real.pi)
      _ = (-Real.pi + Real.pi) + Real.pi :=
        (add_assoc (-Real.pi) Real.pi Real.pi).symm
      _ = 0 + Real.pi :=
        congrArg (fun r : ℝ => r + Real.pi) (neg_add_cancel Real.pi)
      _ = Real.pi :=
        zero_add Real.pi
  have hθ_pi : θ ∈ Set.Ioc (-Real.pi) Real.pi :=
    And.intro hθ.1
      (Eq.subst
        (motive := fun r : ℝ => θ ≤ r)
        hupper
        hθ.2)
  exact
    Real.principalAngle_zero_twoPi_distance_le_intDistance hθ_pi k

/-- Principal-interval control of a raw increment makes the zero `2πℤ`
lattice point closest to that increment. -/
theorem Complex.realPhase_integerIncrement_zero_lattice_closest_of_mem_principal
    (φ : ℝ → ℝ)
    {n : ℕ}
    (hprincipal :
      Complex.realPhase_integerIncrement φ n ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
    (k : ℤ) :
    ‖Complex.realPhase_integerIncrement φ n - (2 * Real.pi * (0 : ℝ))‖ ≤
      ‖Complex.realPhase_integerIncrement φ n - (2 * Real.pi * (k : ℝ))‖ :=
  Real.periodicPrincipalAngle_zero_twoPi_distance_le_intDistance hprincipal k

/-- If a raw adjacent increment already lies in the principal `toIocMod`
interval, then reduction does not change it. -/
theorem Complex.realPhase_reducedIntegerIncrement_eq_raw_of_mem_principal
    (φ : ℝ → ℝ)
    {n : ℕ}
    (hprincipal :
      Complex.realPhase_integerIncrement φ n ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    Complex.realPhase_reducedIntegerIncrement φ n =
      Complex.realPhase_integerIncrement φ n := by
  unfold Complex.realPhase_reducedIntegerIncrement
  exact
    (toIocMod_eq_self Real.two_pi_pos).mpr hprincipal

/-- Principal-interval control transfers raw monotonicity to reduced
monotonicity. -/
theorem Complex.realPhase_reducedIntegerIncrementMonotoneOn_of_raw_principal
    (φ : ℝ → ℝ)
    {a b : ℕ}
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          Complex.realPhase_integerIncrement φ n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b := by
  match hinc_mono with
  | Or.inl hmono =>
      exact Or.inl
        (fun m hm n hn hmn =>
          have hm_eq :
              Complex.realPhase_reducedIntegerIncrement φ m =
                Complex.realPhase_integerIncrement φ m :=
            Complex.realPhase_reducedIntegerIncrement_eq_raw_of_mem_principal
              φ (hprincipal m hm)
          have hn_eq :
              Complex.realPhase_reducedIntegerIncrement φ n =
                Complex.realPhase_integerIncrement φ n :=
            Complex.realPhase_reducedIntegerIncrement_eq_raw_of_mem_principal
              φ (hprincipal n hn)
          have hraw :
              Complex.realPhase_integerIncrement φ m ≤
                Complex.realPhase_integerIncrement φ n :=
            hmono hm hn hmn
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤ Complex.realPhase_reducedIntegerIncrement φ n)
            hm_eq.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                Complex.realPhase_integerIncrement φ m ≤ right)
              hn_eq.symm
              hraw))
  | Or.inr hanti =>
      exact Or.inr
        (fun m hm n hn hmn =>
          have hm_eq :
              Complex.realPhase_reducedIntegerIncrement φ m =
                Complex.realPhase_integerIncrement φ m :=
            Complex.realPhase_reducedIntegerIncrement_eq_raw_of_mem_principal
              φ (hprincipal m hm)
          have hn_eq :
              Complex.realPhase_reducedIntegerIncrement φ n =
                Complex.realPhase_integerIncrement φ n :=
            Complex.realPhase_reducedIntegerIncrement_eq_raw_of_mem_principal
              φ (hprincipal n hn)
          have hraw :
              Complex.realPhase_integerIncrement φ n ≤
                Complex.realPhase_integerIncrement φ m :=
            hanti hm hn hmn
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤ Complex.realPhase_reducedIntegerIncrement φ m)
            hn_eq.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                Complex.realPhase_integerIncrement φ n ≤ right)
              hm_eq.symm
              hraw))

end

end LFunctions
end Boundary
