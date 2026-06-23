import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.KernelEnvelope

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

/-- The fixed scalar width used by the degree-polynomial normalizer is
positive. -/
theorem finiteOrderPL_degreePolynomialScalarWidth_pos
    (N : ℕ) :
    0 < (2 * ((N + 1 : ℕ) : ℝ))⁻¹ := by
  have hsucc_pos_nat : 0 < N + 1 :=
    Nat.succ_pos N
  have hsucc_pos_real : 0 < ((N + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr hsucc_pos_nat
  have hden_pos : 0 < 2 * ((N + 1 : ℕ) : ℝ) :=
    mul_pos zero_lt_two hsucc_pos_real
  exact inv_pos.mpr hden_pos

/-- Nonnegative form of the fixed scalar width used by the degree-polynomial
normalizer. -/
theorem finiteOrderPL_degreePolynomialScalarWidth_nonneg
    (N : ℕ) :
    0 ≤ (2 * ((N + 1 : ℕ) : ℝ))⁻¹ :=
  le_of_lt (finiteOrderPL_degreePolynomialScalarWidth_pos N)

/-- The fixed scalar width is strictly smaller than one. -/
theorem finiteOrderPL_degreePolynomialScalarWidth_lt_one
    (N : ℕ) :
    (2 * ((N + 1 : ℕ) : ℝ))⁻¹ < 1 := by
  have hsucc_pos_nat : 0 < N + 1 :=
    Nat.succ_pos N
  have hsucc_pos_real : 0 < ((N + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr hsucc_pos_nat
  have hsucc_ge_one_nat : 1 ≤ N + 1 :=
    Nat.succ_le_succ (Nat.zero_le N)
  have hsucc_ge_one_real : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr hsucc_ge_one_nat
  have htwo_le_den :
      (2 : ℝ) ≤ 2 * ((N + 1 : ℕ) : ℝ) := by
    calc
      (2 : ℝ) = 2 * 1 := (mul_one 2).symm
      _ ≤ 2 * ((N + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsucc_ge_one_real (le_of_lt zero_lt_two)
  have hone_lt_den :
      (1 : ℝ) < 2 * ((N + 1 : ℕ) : ℝ) :=
    lt_of_lt_of_le one_lt_two htwo_le_den
  exact inv_lt_one_of_one_lt₀ hone_lt_den

/-- The linear factor `2*k*B` is subunit for the degree-polynomial scalar
width whenever `k < N + 1`. -/
theorem finiteOrderPL_two_mul_nat_mul_scalarWidth_lt_one
    (N k : ℕ)
    (hk : k < N + 1) :
    2 * (k : ℝ) * (2 * ((N + 1 : ℕ) : ℝ))⁻¹ < 1 := by
  let K : ℝ := 2 * ((N + 1 : ℕ) : ℝ)
  have hK_pos : 0 < K := by
    have hsucc_pos_nat : 0 < N + 1 :=
      Nat.succ_pos N
    have hsucc_pos_real : 0 < ((N + 1 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr hsucc_pos_nat
    exact mul_pos zero_lt_two hsucc_pos_real
  have hk_real : (k : ℝ) < ((N + 1 : ℕ) : ℝ) :=
    Nat.cast_lt.mpr hk
  have hnum_lt :
      2 * (k : ℝ) < K := by
    have hmul :
        2 * (k : ℝ) < 2 * ((N + 1 : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_left hk_real zero_lt_two
    exact hmul
  have hdiv :
      (2 * (k : ℝ)) / K < 1 :=
    (div_lt_one hK_pos).mpr hnum_lt
  have hleft :
      2 * (k : ℝ) * (2 * ((N + 1 : ℕ) : ℝ))⁻¹ =
        (2 * (k : ℝ)) / K := by
    calc
      2 * (k : ℝ) * (2 * ((N + 1 : ℕ) : ℝ))⁻¹ =
          (2 * (k : ℝ)) * K⁻¹ := rfl
      _ = (2 * (k : ℝ)) / K :=
        (div_eq_mul_inv (2 * (k : ℝ)) K).symm
  exact
    Eq.subst
      (motive := fun T : ℝ => T < 1)
      hleft.symm
      hdiv

/-- Fixed-width smallness input for the tangent-width recursion. -/
theorem finiteOrderPL_two_mul_nat_mul_scalarWidth_sq_lt_one
    (N k : ℕ)
    (hk : k < N + 1) :
    2 * (k : ℝ) *
        (2 * ((N + 1 : ℕ) : ℝ))⁻¹ *
        (2 * ((N + 1 : ℕ) : ℝ))⁻¹ < 1 := by
  let B : ℝ := (2 * ((N + 1 : ℕ) : ℝ))⁻¹
  have hlinear :
      2 * (k : ℝ) * B < 1 :=
    finiteOrderPL_two_mul_nat_mul_scalarWidth_lt_one N k hk
  have hlinear_nonneg :
      0 ≤ 2 * (k : ℝ) * B := by
    have hk_nonneg : 0 ≤ (k : ℝ) :=
      Nat.cast_nonneg k
    have htwo_k_nonneg : 0 ≤ 2 * (k : ℝ) :=
      mul_nonneg (le_of_lt zero_lt_two) hk_nonneg
    have hB_nonneg : 0 ≤ B :=
      finiteOrderPL_degreePolynomialScalarWidth_nonneg N
    exact mul_nonneg htwo_k_nonneg hB_nonneg
  have hB_le_one : B ≤ 1 :=
    le_of_lt (finiteOrderPL_degreePolynomialScalarWidth_lt_one N)
  have hmul_le :
      (2 * (k : ℝ) * B) * B ≤
        (2 * (k : ℝ) * B) * 1 :=
    mul_le_mul_of_nonneg_left hB_le_one hlinear_nonneg
  have hright :
      (2 * (k : ℝ) * B) * 1 = 2 * (k : ℝ) * B :=
    mul_one (2 * (k : ℝ) * B)
  have htarget_le :
      (2 * (k : ℝ) * B) * B < 1 :=
    lt_of_le_of_lt
      (Eq.subst
        (motive := fun T : ℝ => (2 * (k : ℝ) * B) * B ≤ T)
        hright
        hmul_le)
      hlinear
  exact htarget_le

/-- Fixed-width smallness packaged in the form consumed by the scalar
tangent-width recursion. -/
theorem finiteOrderPL_sectorPowerWidth_small_input
    (N : ℕ) :
    ∀ k : ℕ, k < N →
      2 * (k : ℝ) *
          (2 * ((N + 1 : ℕ) : ℝ))⁻¹ *
          (2 * ((N + 1 : ℕ) : ℝ))⁻¹ < 1 :=
  fun k hk =>
    finiteOrderPL_two_mul_nat_mul_scalarWidth_sq_lt_one
      N k (lt_trans hk (Nat.lt_succ_self N))

/-- A linear width bound and a loss estimate give the exact denominator margin
needed for one tangent-width recursion step. -/
theorem finiteOrderPL_sectorPowerWidth_step_margin_of_linear_bound
    {B : ℝ}
    (k : ℕ)
    (hB_nonneg : 0 ≤ B)
    (hwidth :
      sectorPowerWidth B k ≤ 2 * (k : ℝ) * B)
    (hloss :
      (2 * ((k + 1 : ℕ) : ℝ) * B) *
          (sectorPowerWidth B k * B) ≤ B) :
    sectorPowerWidth B k + B ≤
      (2 * ((k + 1 : ℕ) : ℝ) * B) *
        (1 - sectorPowerWidth B k * B) := by
  let T : ℝ := sectorPowerWidth B k
  let L : ℝ := 2 * ((k + 1 : ℕ) : ℝ) * B
  have hleft_linear :
      T + B ≤ 2 * (k : ℝ) * B + B :=
    add_le_add_right hwidth B
  have htwo_k_plus_one :
      2 * (k : ℝ) * B + B ≤ L - B := by
    have hsucc_cast :
        ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 :=
      Nat.cast_add_one k
    have hL_eq :
        L = (2 * (k : ℝ) * B + B) + B := by
      calc
        L = 2 * ((k + 1 : ℕ) : ℝ) * B := rfl
        _ = 2 * ((k : ℝ) + 1) * B :=
          congrArg (fun X : ℝ => 2 * X * B) hsucc_cast
        _ = (2 * (k : ℝ) + 2 * 1) * B :=
          congrArg (fun X : ℝ => X * B) (mul_add 2 (k : ℝ) 1)
        _ = (2 * (k : ℝ) + 2) * B :=
          congrArg (fun X : ℝ => (2 * (k : ℝ) + X) * B) (mul_one 2)
        _ = 2 * (k : ℝ) * B + 2 * B :=
          add_mul (2 * (k : ℝ)) 2 B
        _ = 2 * (k : ℝ) * B + (B + B) := by
          have htwo_B : 2 * B = B + B := by
            calc
              2 * B = (1 + 1) * B := by
                rfl
              _ = 1 * B + 1 * B := add_mul 1 1 B
              _ = B + B :=
                Eq.trans
                  (congrArg (fun X : ℝ => X + 1 * B) (one_mul B))
                  (congrArg (fun X : ℝ => B + X) (one_mul B))
          exact congrArg (fun X : ℝ => 2 * (k : ℝ) * B + X) htwo_B
        _ = (2 * (k : ℝ) * B + B) + B :=
          add_assoc (2 * (k : ℝ) * B) B B
    have hsub_eq :
        L - B = 2 * (k : ℝ) * B + B := by
      calc
        L - B = ((2 * (k : ℝ) * B + B) + B) - B :=
          congrArg (fun X : ℝ => X - B) hL_eq
        _ = 2 * (k : ℝ) * B + B :=
          add_sub_cancel_right (2 * (k : ℝ) * B + B) B
    exact
      Eq.subst
        (motive := fun X : ℝ => 2 * (k : ℝ) * B + B ≤ X)
        hsub_eq.symm
        (le_of_eq rfl)
  have hloss_transport :
      L - B ≤ L - L * (T * B) := by
    exact sub_le_sub_left hloss L
  have hright_eq :
      L - L * (T * B) = L * (1 - T * B) := by
    calc
      L - L * (T * B) = L * 1 - L * (T * B) :=
        congrArg (fun X : ℝ => X - L * (T * B)) (mul_one L).symm
      _ = L * (1 - T * B) :=
        (mul_sub L 1 (T * B)).symm
  exact
    le_trans hleft_linear
      (le_trans htwo_k_plus_one
        (Eq.subst
          (motive := fun X : ℝ => L - B ≤ X)
          hright_eq
          hloss_transport))

/-- Linear width control transports the scalar loss estimate needed in the
tangent-width denominator margin. -/
theorem finiteOrderPL_sectorPowerWidth_loss_of_linear_bound
    {B : ℝ}
    (k : ℕ)
    (hB_nonneg : 0 ≤ B)
    (hwidth :
      sectorPowerWidth B k ≤ 2 * (k : ℝ) * B)
    (hloss_scalar :
      (2 * ((k + 1 : ℕ) : ℝ) * B) *
          (2 * (k : ℝ) * B * B) ≤ B) :
    (2 * ((k + 1 : ℕ) : ℝ) * B) *
        (sectorPowerWidth B k * B) ≤ B := by
  let L : ℝ := 2 * ((k + 1 : ℕ) : ℝ) * B
  have hL_nonneg : 0 ≤ L := by
    have hsucc_nonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) :=
      Nat.cast_nonneg (k + 1)
    have htwo_succ_nonneg : 0 ≤ 2 * ((k + 1 : ℕ) : ℝ) :=
      mul_nonneg (le_of_lt zero_lt_two) hsucc_nonneg
    exact mul_nonneg htwo_succ_nonneg hB_nonneg
  have hwidth_times :
      sectorPowerWidth B k * B ≤ (2 * (k : ℝ) * B) * B :=
    mul_le_mul_of_nonneg_right hwidth hB_nonneg
  have hright_eq :
      (2 * (k : ℝ) * B) * B =
        2 * (k : ℝ) * B * B := by
    rfl
  have hwidth_loss :
      sectorPowerWidth B k * B ≤ 2 * (k : ℝ) * B * B :=
    Eq.subst
      (motive := fun X : ℝ => sectorPowerWidth B k * B ≤ X)
      hright_eq
      hwidth_times
  have hscaled :
      L * (sectorPowerWidth B k * B) ≤
        L * (2 * (k : ℝ) * B * B) :=
    mul_le_mul_of_nonneg_left hwidth_loss hL_nonneg
  exact le_trans hscaled hloss_scalar

/-- One tangent-width denominator margin from a linear width bound and the
corresponding scalar loss estimate. -/
theorem finiteOrderPL_sectorPowerWidth_step_margin_of_linear_bound_and_loss
    {B : ℝ}
    (k : ℕ)
    (hB_nonneg : 0 ≤ B)
    (hwidth :
      sectorPowerWidth B k ≤ 2 * (k : ℝ) * B)
    (hloss_scalar :
      (2 * ((k + 1 : ℕ) : ℝ) * B) *
          (2 * (k : ℝ) * B * B) ≤ B) :
    sectorPowerWidth B k + B ≤
      (2 * ((k + 1 : ℕ) : ℝ) * B) *
        (1 - sectorPowerWidth B k * B) :=
  finiteOrderPL_sectorPowerWidth_step_margin_of_linear_bound
    k hB_nonneg hwidth
    (finiteOrderPL_sectorPowerWidth_loss_of_linear_bound
      k hB_nonneg hwidth hloss_scalar)

/-- Fixed scalar loss estimate for the degree-polynomial width recursion. -/
theorem finiteOrderPL_sectorPowerWidth_loss_scalar
    (N k : ℕ)
    (hk : k < N) :
    (2 * ((k + 1 : ℕ) : ℝ) *
          (2 * ((N + 1 : ℕ) : ℝ))⁻¹) *
        (2 * (k : ℝ) *
          (2 * ((N + 1 : ℕ) : ℝ))⁻¹ *
          (2 * ((N + 1 : ℕ) : ℝ))⁻¹) ≤
      (2 * ((N + 1 : ℕ) : ℝ))⁻¹ := by
  let B : ℝ := (2 * ((N + 1 : ℕ) : ℝ))⁻¹
  let X : ℝ := 2 * ((k + 1 : ℕ) : ℝ) * B
  let Y : ℝ := 2 * (k : ℝ) * B
  have hB_nonneg : 0 ≤ B :=
    finiteOrderPL_degreePolynomialScalarWidth_nonneg N
  have hX_nonneg : 0 ≤ X := by
    have hsucc_nonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) :=
      Nat.cast_nonneg (k + 1)
    have htwo_succ_nonneg : 0 ≤ 2 * ((k + 1 : ℕ) : ℝ) :=
      mul_nonneg (le_of_lt zero_lt_two) hsucc_nonneg
    exact mul_nonneg htwo_succ_nonneg hB_nonneg
  have hY_nonneg : 0 ≤ Y := by
    have hk_nonneg : 0 ≤ (k : ℝ) :=
      Nat.cast_nonneg k
    have htwo_k_nonneg : 0 ≤ 2 * (k : ℝ) :=
      mul_nonneg (le_of_lt zero_lt_two) hk_nonneg
    exact mul_nonneg htwo_k_nonneg hB_nonneg
  have hX_le_one : X ≤ 1 :=
    le_of_lt
      (finiteOrderPL_two_mul_nat_mul_scalarWidth_lt_one
        N (k + 1) (Nat.succ_lt_succ hk))
  have hY_le_one : Y ≤ 1 :=
    le_of_lt
      (finiteOrderPL_two_mul_nat_mul_scalarWidth_lt_one
        N k (lt_trans hk (Nat.lt_succ_self N)))
  have hXY_le_one : X * Y ≤ 1 := by
    have hmul :
        X * Y ≤ 1 * 1 :=
      mul_le_mul hX_le_one hY_le_one hY_nonneg zero_le_one
    exact
      Eq.subst
        (motive := fun T : ℝ => X * Y ≤ T)
        (mul_one 1)
        hmul
  have hscaled :
      (X * Y) * B ≤ 1 * B :=
    mul_le_mul_of_nonneg_right hXY_le_one hB_nonneg
  have hright :
      1 * B = B :=
    one_mul B
  have hleft :
      (2 * ((k + 1 : ℕ) : ℝ) * B) *
          (2 * (k : ℝ) * B * B) =
        (X * Y) * B := by
    calc
      (2 * ((k + 1 : ℕ) : ℝ) * B) *
          (2 * (k : ℝ) * B * B) =
          X * (Y * B) := rfl
      _ = (X * Y) * B :=
        (mul_assoc X Y B).symm
  exact
    Eq.subst
      (motive := fun T : ℝ => T ≤ B)
      hleft.symm
      (Eq.subst
        (motive := fun T : ℝ => (X * Y) * B ≤ T)
        hright
        hscaled)

/-- Linear control, nonnegativity, and subcriticality for the fixed
degree-polynomial scalar width through degree `N`. -/
theorem finiteOrderPL_sectorPowerWidth_fixed_linear_package
    (N : ℕ) :
    let B : ℝ := (2 * ((N + 1 : ℕ) : ℝ))⁻¹
    (∀ k : ℕ, k ≤ N → sectorPowerWidth B k ≤ 2 * (k : ℝ) * B) ∧
      (∀ k : ℕ, k ≤ N → 0 ≤ sectorPowerWidth B k) ∧
      (∀ k : ℕ, k < N → sectorPowerWidth B k * B < 1) := by
  let B : ℝ := (2 * ((N + 1 : ℕ) : ℝ))⁻¹
  have hB_nonneg : 0 ≤ B :=
    finiteOrderPL_degreePolynomialScalarWidth_nonneg N
  have hstep :
      ∀ n : ℕ,
        n ≤ N →
        (∀ k : ℕ, k ≤ n → sectorPowerWidth B k ≤ 2 * (k : ℝ) * B) ∧
          (∀ k : ℕ, k ≤ n → 0 ≤ sectorPowerWidth B k) ∧
          (∀ k : ℕ, k < n → sectorPowerWidth B k * B < 1) := by
    intro n
    induction n with
    | zero =>
        intro _hn
        have hwidth0 :
            sectorPowerWidth B 0 ≤ 2 * (0 : ℝ) * B := by
          have hleft : sectorPowerWidth B 0 = 0 :=
            sectorPowerWidth_zero B
          have hright : 2 * (0 : ℝ) * B = 0 := by
            calc
              2 * (0 : ℝ) * B = 0 * B := by
                rfl
              _ = 0 := zero_mul B
          exact
            Eq.subst
              (motive := fun T : ℝ => T ≤ 2 * (0 : ℝ) * B)
              hleft
              (Eq.subst
                (motive := fun T : ℝ => 0 ≤ T)
                hright.symm
                (le_of_eq rfl))
        have hnonneg0 :
            0 ≤ sectorPowerWidth B 0 :=
          Eq.subst
            (motive := fun T : ℝ => 0 ≤ T)
            (sectorPowerWidth_zero B).symm
            (le_of_eq rfl)
        exact
          ⟨fun k hk =>
              match Nat.eq_zero_of_le_zero hk with
              | rfl => hwidth0,
            fun k hk =>
              match Nat.eq_zero_of_le_zero hk with
              | rfl => hnonneg0,
            fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
    | succ n ih =>
        intro hsucc_le_N
        have hn_le_N : n ≤ N :=
          Nat.le_trans (Nat.le_succ n) hsucc_le_N
        have hprev :
            (∀ k : ℕ, k ≤ n → sectorPowerWidth B k ≤ 2 * (k : ℝ) * B) ∧
              (∀ k : ℕ, k ≤ n → 0 ≤ sectorPowerWidth B k) ∧
              (∀ k : ℕ, k < n → sectorPowerWidth B k * B < 1) :=
          ih hn_le_N
        have hn_lt_N : n < N := by
          exact Nat.lt_of_succ_le hsucc_le_N
        have hn_width :
            sectorPowerWidth B n ≤ 2 * (n : ℝ) * B :=
          hprev.1 n le_rfl
        have hn_subcritical :
            sectorPowerWidth B n * B < 1 :=
          sectorPowerWidth_mul_lt_one_of_le_linear
            hB_nonneg hn_width
            (finiteOrderPL_two_mul_nat_mul_scalarWidth_sq_lt_one
              N n (lt_trans hn_lt_N (Nat.lt_succ_self N)))
        have hsucc_width :
            sectorPowerWidth B (n + 1) ≤
              2 * ((n + 1 : ℕ) : ℝ) * B := by
          have hmargin :
              sectorPowerWidth B n + B ≤
                (2 * ((n + 1 : ℕ) : ℝ) * B) *
                  (1 - sectorPowerWidth B n * B) :=
            finiteOrderPL_sectorPowerWidth_step_margin_of_linear_bound_and_loss
              n hB_nonneg hn_width
              (finiteOrderPL_sectorPowerWidth_loss_scalar N n hn_lt_N)
          have hstep_width :
              sectorPowerWidthStep (sectorPowerWidth B n) B ≤
                2 * ((n + 1 : ℕ) : ℝ) * B :=
            sectorPowerWidthStep_le_of_denominator_margin
              hn_subcritical hmargin
          exact
            Eq.subst
              (motive := fun T : ℝ =>
                T ≤ 2 * ((n + 1 : ℕ) : ℝ) * B)
              (sectorPowerWidth_succ B n).symm
              hstep_width
        have hsucc_nonneg :
            0 ≤ sectorPowerWidth B (n + 1) :=
          sectorPowerWidth_nonneg_of_previous_step
            hB_nonneg (hprev.2.1 n le_rfl) hn_subcritical
        exact
          ⟨fun k hk =>
              match Nat.eq_or_lt_of_le hk with
              | Or.inl heq =>
                  Eq.subst
                    (motive := fun T : ℕ =>
                      sectorPowerWidth B k ≤ 2 * (T : ℝ) * B)
                    heq.symm
                    hsucc_width
              | Or.inr hlt =>
                  hprev.1 k (Nat.le_of_lt_succ hlt),
            fun k hk =>
              match Nat.eq_or_lt_of_le hk with
              | Or.inl heq =>
                  Eq.subst
                    (motive := fun T : ℕ => 0 ≤ sectorPowerWidth B T)
                    heq
                    hsucc_nonneg
              | Or.inr hlt =>
                  hprev.2.1 k (Nat.le_of_lt_succ hlt),
            fun k hk =>
              match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with
              | Or.inl heq =>
                  Eq.subst
                    (motive := fun T : ℕ => sectorPowerWidth B T * B < 1)
                    heq
                    hn_subcritical
              | Or.inr hlt =>
          hprev.2.2 k hlt⟩
  exact hstep N le_rfl

/-- The accumulated real-part constant for the fixed degree-polynomial scalar
width is positive through degree `N`. -/
theorem finiteOrderPL_sectorPowerRealConstant_fixed_pos
    (N : ℕ) :
    0 <
      sectorPowerRealConstant
        ((2 * ((N + 1 : ℕ) : ℝ))⁻¹) N := by
  let B : ℝ := (2 * ((N + 1 : ℕ) : ℝ))⁻¹
  have hpack :
      (∀ k : ℕ, k ≤ N → sectorPowerWidth B k ≤ 2 * (k : ℝ) * B) ∧
        (∀ k : ℕ, k ≤ N → 0 ≤ sectorPowerWidth B k) ∧
        (∀ k : ℕ, k < N → sectorPowerWidth B k * B < 1) :=
    finiteOrderPL_sectorPowerWidth_fixed_linear_package N
  exact
    sectorPowerRealConstant_pos_of_subcritical_steps B N hpack.2.2

/-- Arbitrary-degree lower real-part bound for the degree-polynomial normalizer
on the closed upper tail. -/
theorem verticalStripUpperTailDegreePolynomialKernel_re_lower_on_upperTail
    (a b : ℝ)
    (N : ℕ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hz_im : 1 ≤ z.im) :
    let B : ℝ := (2 * ((N + 1 : ℕ) : ℝ))⁻¹
    sectorPowerRealConstant B N *
        (verticalStripUpperTailDegreePolynomialBase a b N z).re ^ N ≤
      (verticalStripUpperTailDegreePolynomialKernel a b N z).re := by
  let B : ℝ := (2 * ((N + 1 : ℕ) : ℝ))⁻¹
  let W : ℂ := verticalStripUpperTailDegreePolynomialBase a b N z
  have hW_re_nonneg : 0 ≤ W.re :=
    le_of_lt
      (verticalStripUpperTailDegreePolynomialBase_re_pos_on_upperTail
        a b N hz_im)
  have hB_nonneg : 0 ≤ B :=
    finiteOrderPL_degreePolynomialScalarWidth_nonneg N
  have hW_im :
      |W.im| ≤ B * W.re :=
    verticalStripUpperTailDegreePolynomialBase_im_abs_le_inv_two_degree_mul_re
      a b N hza hzb hz_im
  have hpack :
      (∀ k : ℕ, k ≤ N → sectorPowerWidth B k ≤ 2 * (k : ℝ) * B) ∧
        (∀ k : ℕ, k ≤ N → 0 ≤ sectorPowerWidth B k) ∧
        (∀ k : ℕ, k < N → sectorPowerWidth B k * B < 1) :=
    finiteOrderPL_sectorPowerWidth_fixed_linear_package N
  have hpow :
      (sectorPowerRealConstant B N * W.re ^ N ≤ (W ^ N).re) ∧
        (0 ≤ (W ^ N).re) ∧
        (|(W ^ N).im| ≤ sectorPowerWidth B N * (W ^ N).re) :=
    complex_pow_sector_and_re_lower_of_scalar_widths
      hW_re_nonneg hB_nonneg hW_im N
      (fun k hk => hpack.2.1 k (le_of_lt hk))
      hpack.2.2
  have hkernel :
      verticalStripUpperTailDegreePolynomialKernel a b N z = W ^ N :=
    verticalStripUpperTailDegreePolynomialKernel_eq a b N z
  exact
    Eq.subst
      (motive := fun T : ℂ =>
        sectorPowerRealConstant B N * W.re ^ N ≤ T.re)
      hkernel.symm
      hpow.1

/-- Positive lower-bound constant accompanying the degree-polynomial kernel
real-part estimate. -/
theorem verticalStripUpperTailDegreePolynomialKernel_re_lower_constant_pos
    (N : ℕ) :
    0 <
      sectorPowerRealConstant
        ((2 * ((N + 1 : ℕ) : ℝ))⁻¹) N :=
  finiteOrderPL_sectorPowerRealConstant_fixed_pos N

/-- The polynomial-normalizer boundary coefficient is positive when the
original boundary exponent is positive. -/
theorem finiteOrderPL_degreePolynomialBoundaryCoefficient_pos
    (B₀ : ℝ)
    (m : ℕ)
    (hB₀ : 0 < B₀) :
    0 <
      B₀ *
        (sectorPowerRealConstant
          ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m)⁻¹ := by
  have hc_pos :
      0 <
        sectorPowerRealConstant
          ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m :=
    finiteOrderPL_sectorPowerRealConstant_fixed_pos m
  have hcinv_pos :
      0 <
        (sectorPowerRealConstant
          ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m)⁻¹ :=
    inv_pos.mpr hc_pos
  exact mul_pos hB₀ hcinv_pos

/-- The degree-polynomial kernel dominates the vertical finite-order boundary
envelope on the closed upper tail after scaling by the reciprocal of its
positive sector constant. -/
theorem verticalStripUpperTailDegreePolynomialKernel_dominates_boundary_envelope
    (a b B₀ : ℝ)
    (m : ℕ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hz_im : 1 ≤ z.im)
    (hB₀_nonneg : 0 ≤ B₀) :
    let c : ℝ :=
      sectorPowerRealConstant
        ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
    B₀ * (1 + ‖z.im‖) ^ m ≤
      (B₀ * c⁻¹) *
        (verticalStripUpperTailDegreePolynomialKernel a b m z).re := by
  let c : ℝ :=
    sectorPowerRealConstant
      ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
  let W : ℂ := verticalStripUpperTailDegreePolynomialBase a b m z
  have hc_pos : 0 < c :=
    finiteOrderPL_sectorPowerRealConstant_fixed_pos m
  have hc_inv_nonneg : 0 ≤ c⁻¹ :=
    inv_nonneg.mpr (le_of_lt hc_pos)
  have hheight :
      (1 + ‖z.im‖) ^ m ≤ W.re ^ m :=
    verticalStripUpperTailDegreePolynomialBase_one_add_im_norm_pow_le_re_pow
      a b m hz_im
  have hkernel_lower :
      c * W.re ^ m ≤
        (verticalStripUpperTailDegreePolynomialKernel a b m z).re :=
    verticalStripUpperTailDegreePolynomialKernel_re_lower_on_upperTail
      a b m hza hzb hz_im
  have hWpow_le_kernel_scaled :
      W.re ^ m ≤
        c⁻¹ *
          (verticalStripUpperTailDegreePolynomialKernel a b m z).re := by
    have hscaled :
        c⁻¹ * (c * W.re ^ m) ≤
          c⁻¹ *
            (verticalStripUpperTailDegreePolynomialKernel a b m z).re :=
      mul_le_mul_of_nonneg_left hkernel_lower hc_inv_nonneg
    have hleft :
        c⁻¹ * (c * W.re ^ m) = W.re ^ m := by
      calc
        c⁻¹ * (c * W.re ^ m) = (c⁻¹ * c) * W.re ^ m :=
          (mul_assoc c⁻¹ c (W.re ^ m)).symm
        _ = 1 * W.re ^ m :=
          congrArg (fun T : ℝ => T * W.re ^ m) (inv_mul_cancel₀ hc_pos.ne')
        _ = W.re ^ m := one_mul (W.re ^ m)
    exact
      Eq.subst
        (motive := fun T : ℝ =>
          T ≤ c⁻¹ *
            (verticalStripUpperTailDegreePolynomialKernel a b m z).re)
        hleft
        hscaled
  have hheight_scaled :
      B₀ * (1 + ‖z.im‖) ^ m ≤ B₀ * W.re ^ m :=
    mul_le_mul_of_nonneg_left hheight hB₀_nonneg
  have hkernel_scaled :
      B₀ * W.re ^ m ≤
        B₀ *
          (c⁻¹ *
            (verticalStripUpperTailDegreePolynomialKernel a b m z).re) :=
    mul_le_mul_of_nonneg_left hWpow_le_kernel_scaled hB₀_nonneg
  have hright :
      B₀ *
          (c⁻¹ *
            (verticalStripUpperTailDegreePolynomialKernel a b m z).re) =
        (B₀ * c⁻¹) *
          (verticalStripUpperTailDegreePolynomialKernel a b m z).re :=
    (mul_assoc B₀ c⁻¹
      (verticalStripUpperTailDegreePolynomialKernel a b m z).re).symm
  exact
    le_trans hheight_scaled
      (Eq.subst
        (motive := fun T : ℝ => B₀ * W.re ^ m ≤ T)
        hright
        hkernel_scaled)

/-- Boundary finite-order control gives unit control of the degree-polynomial
bounded normalized factor on the closed upper tail. -/
theorem verticalStripUpperTailDegreePolynomialBoundedFactor_boundary_norm_le_one_on_upperTail
    (f : ℂ → ℂ)
    (a b A₀ B₀ : ℝ)
    (m : ℕ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hz_im : 1 ≤ z.im)
    (hA₀ : 0 < A₀)
    (hB₀_nonneg : 0 ≤ B₀)
    (hboundary :
      ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m)) :
    let c : ℝ :=
      sectorPowerRealConstant
        ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
    ‖verticalStripUpperTailDegreePolynomialBoundedFactor
        f a b A₀ (B₀ * c⁻¹) m z‖ ≤ 1 := by
  let c : ℝ :=
    sectorPowerRealConstant
      ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
  have hdominates :
      B₀ * (1 + ‖z.im‖) ^ m ≤
        (B₀ * c⁻¹) *
          (verticalStripUpperTailDegreePolynomialKernel a b m z).re :=
    verticalStripUpperTailDegreePolynomialKernel_dominates_boundary_envelope
      a b B₀ m hza hzb hz_im hB₀_nonneg
  exact
    verticalStripUpperTailDegreePolynomialBoundedFactor_boundary_norm_le_one_of_re_dominates
      f a b A₀ B₀ (B₀ * c⁻¹) m m z hA₀ hboundary hdominates

/-- The mixed cosine/degree-polynomial bounded factor has unit control on the
two upper vertical boundary rays, uniformly in the positive cosine damping
parameter. -/
theorem verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_vertical_boundary_norm_le_one
    (f : ℂ → ℂ)
    (a b d A₀ B₀ ε : ℝ)
    (m : ℕ)
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_nonneg : 0 ≤ ε)
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m)) :
    let c : ℝ :=
      sectorPowerRealConstant
        ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
    (∀ z : ℂ,
      z.re = a →
      1 ≤ z.im →
      ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
          f a b d A₀ (B₀ * c⁻¹) ε m z‖ ≤ 1) ∧
    (∀ z : ℂ,
      z.re = b →
      1 ≤ z.im →
      ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
          f a b d A₀ (B₀ * c⁻¹) ε m z‖ ≤ 1) := by
  let c : ℝ :=
    sectorPowerRealConstant
      ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
  have hB₀_nonneg : 0 ≤ B₀ :=
    le_of_lt hB₀
  constructor
  · intro z hz_re hz_im
    have hza : a ≤ z.re :=
      le_of_eq hz_re.symm
    have hzb : z.re ≤ b :=
      le_trans (le_of_eq hz_re) (le_of_lt hab)
    have hboundary :
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m) :=
      hleft z hz_re (upperTail_im_norm_ge_one z hz_im)
    exact
      verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_boundary_norm_le_one_of_re_dominates
        f a b d A₀ B₀ (B₀ * c⁻¹) ε m m z
        hab hd_pos hd_threshold hε_nonneg hza hzb hA₀ hboundary
        (verticalStripUpperTailDegreePolynomialKernel_dominates_boundary_envelope
          a b B₀ m hza hzb hz_im hB₀_nonneg)
  · intro z hz_re hz_im
    have hza : a ≤ z.re :=
      le_trans (le_of_lt hab) (le_of_eq hz_re.symm)
    have hzb : z.re ≤ b :=
      le_of_eq hz_re
    have hboundary :
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m) :=
      hright z hz_re (upperTail_im_norm_ge_one z hz_im)
    exact
      verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_boundary_norm_le_one_of_re_dominates
        f a b d A₀ B₀ (B₀ * c⁻¹) ε m m z
        hab hd_pos hd_threshold hε_nonneg hza hzb hA₀ hboundary
        (verticalStripUpperTailDegreePolynomialKernel_dominates_boundary_envelope
          a b B₀ m hza hzb hz_im hB₀_nonneg)

/-- On the closed strip, adding the subcritical cosine damping can only reduce
the norm of the degree-polynomial bounded factor. -/
theorem verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_norm_le_degreePolynomial
    (f : ℂ → ℂ)
    (a b d A C ε : ℝ)
    (N : ℕ)
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_nonneg : 0 ≤ ε)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
        f a b d A C ε N z‖ ≤
      ‖verticalStripUpperTailDegreePolynomialBoundedFactor
        f a b A C N z‖ := by
  let K : ℂ := verticalStripUpperTailDegreePolynomialKernel a b N z
  have hdamped :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ ‖f z‖ :=
    verticalStripSubcriticalCosineDampedFamily_norm_le_original_on_closedStrip
      f hab hd_pos hd_threshold hε_nonneg z hza hzb
  have hleft_norm :
      ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
          f a b d A C ε N z‖ =
        ‖A⁻¹‖ *
          (‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ *
            Real.exp (-(C * K.re))) :=
    verticalStripUpperTailDegreePolynomialBoundedFactor_norm_eq
      (verticalStripSubcriticalCosineDampedFamily f a b d ε)
      a b A C N z
  have hright_norm :
      ‖verticalStripUpperTailDegreePolynomialBoundedFactor
          f a b A C N z‖ =
        ‖A⁻¹‖ * (‖f z‖ * Real.exp (-(C * K.re))) :=
    verticalStripUpperTailDegreePolynomialBoundedFactor_norm_eq
      f a b A C N z
  have hexp_nonneg :
      0 ≤ Real.exp (-(C * K.re)) :=
    le_of_lt (Real.exp_pos (-(C * K.re)))
  have hinner :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ *
          Real.exp (-(C * K.re)) ≤
        ‖f z‖ * Real.exp (-(C * K.re)) :=
    mul_le_mul_of_nonneg_right hdamped hexp_nonneg
  have hscale_nonneg : 0 ≤ ‖A⁻¹‖ :=
    norm_nonneg A⁻¹
  have hscaled :
      ‖A⁻¹‖ *
          (‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ *
            Real.exp (-(C * K.re))) ≤
        ‖A⁻¹‖ * (‖f z‖ * Real.exp (-(C * K.re))) :=
    mul_le_mul_of_nonneg_left hinner hscale_nonneg
  exact
    Eq.subst
      (motive := fun L : ℝ =>
        L ≤ ‖verticalStripUpperTailDegreePolynomialBoundedFactor
          f a b A C N z‖)
      hleft_norm.symm
      (Eq.subst
        (motive := fun R : ℝ =>
          ‖A⁻¹‖ *
              (‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ *
                Real.exp (-(C * K.re))) ≤ R)
        hright_norm.symm
        hscaled)

/-- The degree-polynomial kernel has nonnegative real part on the closed upper
tail. -/
theorem verticalStripUpperTailDegreePolynomialKernel_re_nonneg_on_upperTail
    (a b : ℝ)
    (N : ℕ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hz_im : 1 ≤ z.im) :
    0 ≤ (verticalStripUpperTailDegreePolynomialKernel a b N z).re := by
  let B : ℝ := (2 * ((N + 1 : ℕ) : ℝ))⁻¹
  let W : ℂ := verticalStripUpperTailDegreePolynomialBase a b N z
  have hc_pos : 0 < sectorPowerRealConstant B N :=
    finiteOrderPL_sectorPowerRealConstant_fixed_pos N
  have hW_re_pos : 0 < W.re :=
    verticalStripUpperTailDegreePolynomialBase_re_pos_on_upperTail
      a b N hz_im
  have hW_pow_nonneg : 0 ≤ W.re ^ N :=
    pow_nonneg (le_of_lt hW_re_pos) N
  have hleft_nonneg :
      0 ≤ sectorPowerRealConstant B N * W.re ^ N :=
    mul_nonneg (le_of_lt hc_pos) hW_pow_nonneg
  have hlower :
      sectorPowerRealConstant B N * W.re ^ N ≤
        (verticalStripUpperTailDegreePolynomialKernel a b N z).re :=
    verticalStripUpperTailDegreePolynomialKernel_re_lower_on_upperTail
      a b N hza hzb hz_im
  exact le_trans hleft_nonneg hlower

/-- The polynomial exponential factor is bounded by one on the closed upper
tail for a nonnegative coefficient. -/
theorem verticalStripUpperTailDegreePolynomial_exp_le_one_on_upperTail
    (a b C : ℝ)
    (N : ℕ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hz_im : 1 ≤ z.im)
    (hC_nonneg : 0 ≤ C) :
    Real.exp
        (-(C *
          (verticalStripUpperTailDegreePolynomialKernel a b N z).re)) ≤ 1 := by
  have hK_nonneg :
      0 ≤ (verticalStripUpperTailDegreePolynomialKernel a b N z).re :=
    verticalStripUpperTailDegreePolynomialKernel_re_nonneg_on_upperTail
      a b N hza hzb hz_im
  have hprod_nonneg :
      0 ≤ C *
        (verticalStripUpperTailDegreePolynomialKernel a b N z).re :=
    mul_nonneg hC_nonneg hK_nonneg
  have hneg_nonpos :
      -(C * (verticalStripUpperTailDegreePolynomialKernel a b N z).re) ≤ 0 :=
    neg_nonpos.mpr hprod_nonneg
  exact Real.exp_le_one_iff.mpr hneg_nonpos

/-- Eventual top-edge constant control for the mixed normalized factor. -/
theorem verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_eventually_topEdge_bound
    (f : ℂ → ℂ)
    {a b c d D A₀ B₀ ε : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_pos : 0 < ε)
    (hcd : c < d)
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hD :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m)) :
    let q : ℝ :=
      sectorPowerRealConstant
        ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
    ∃ Ctop : ℝ,
      0 < Ctop ∧
      ∀ᶠ R : ℝ in Filter.atTop,
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          z.im = R →
          ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
              f a b d A₀ (B₀ * q⁻¹) ε m z‖ ≤ Ctop := by
  let q : ℝ :=
    sectorPowerRealConstant
      ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
  let Cpoly : ℝ := B₀ * q⁻¹
  match
    verticalStripSubcriticalCosineDampedFamily_eventually_topEdge_open_bound
      f hab hd_pos hd_threshold hε_pos hcd hD
  with
  | ⟨K, hK_pos, htop_open⟩ =>
      let Ctop : ℝ := max (‖A₀⁻¹‖ * K) 1
      have hscale_nonneg : 0 ≤ ‖A₀⁻¹‖ :=
        norm_nonneg A₀⁻¹
      have hscaleK_nonneg : 0 ≤ ‖A₀⁻¹‖ * K :=
        mul_nonneg hscale_nonneg (le_of_lt hK_pos)
      have hCtop_pos : 0 < Ctop :=
        lt_of_lt_of_le zero_lt_one (le_max_right (‖A₀⁻¹‖ * K) 1)
      have hscaleK_le : ‖A₀⁻¹‖ * K ≤ Ctop :=
        le_max_left (‖A₀⁻¹‖ * K) 1
      have hone_le_Ctop : (1 : ℝ) ≤ Ctop :=
        le_max_right (‖A₀⁻¹‖ * K) 1
      have hCpoly_nonneg : 0 ≤ Cpoly := by
        have hq_pos : 0 < q :=
          finiteOrderPL_sectorPowerRealConstant_fixed_pos m
        have hqinv_nonneg : 0 ≤ q⁻¹ :=
          inv_nonneg.mpr (le_of_lt hq_pos)
        exact mul_nonneg (le_of_lt hB₀) hqinv_nonneg
      have hboundary :
          (∀ z : ℂ,
            z.re = a →
            1 ≤ z.im →
            ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                f a b d A₀ Cpoly ε m z‖ ≤ 1) ∧
          (∀ z : ℂ,
            z.re = b →
            1 ≤ z.im →
            ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                f a b d A₀ Cpoly ε m z‖ ≤ 1) :=
        verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_vertical_boundary_norm_le_one
          f a b d A₀ B₀ ε m hab hd_pos hd_threshold (le_of_lt hε_pos)
          hA₀ hB₀ hleft hright
      have hlarge : ∀ᶠ R : ℝ in Filter.atTop, 1 ≤ R :=
        eventually_ge_atTop (1 : ℝ)
      exact
        ⟨Ctop, hCtop_pos,
          (htop_open.and hlarge).mono
            fun R hR z hza hzb hz_im =>
              have hz_im_ge : 1 ≤ z.im :=
                Eq.subst
                  (motive := fun T : ℝ => 1 ≤ T)
                  hz_im.symm
                  hR.2
              match lt_or_eq_of_le hza with
              | Or.inl hza_strict =>
                  match lt_or_eq_of_le hzb with
                  | Or.inl hzb_strict =>
                      have hdamped :
                          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ K :=
                        hR.1 z hza_strict hzb_strict hz_im
                      have hnorm_eq :
                          ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                              f a b d A₀ Cpoly ε m z‖ =
                            ‖A₀⁻¹‖ *
                              (‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ *
                                Real.exp
                                  (-(Cpoly *
                                    (verticalStripUpperTailDegreePolynomialKernel a b m z).re))) :=
                        verticalStripUpperTailDegreePolynomialBoundedFactor_norm_eq
                          (verticalStripSubcriticalCosineDampedFamily f a b d ε)
                          a b A₀ Cpoly m z
                      have hexp_le :
                          Real.exp
                              (-(Cpoly *
                                (verticalStripUpperTailDegreePolynomialKernel a b m z).re)) ≤ 1 :=
                        verticalStripUpperTailDegreePolynomial_exp_le_one_on_upperTail
                          a b Cpoly m hza hzb hz_im_ge hCpoly_nonneg
                      have hinner :
                          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ *
                              Real.exp
                                (-(Cpoly *
                                  (verticalStripUpperTailDegreePolynomialKernel a b m z).re)) ≤
                            K * 1 :=
                        mul_le_mul hdamped hexp_le
                          (le_of_lt (Real.exp_pos
                            (-(Cpoly *
                              (verticalStripUpperTailDegreePolynomialKernel a b m z).re))))
                          (norm_nonneg
                            (verticalStripSubcriticalCosineDampedFamily f a b d ε z))
                      have hscaled :
                          ‖A₀⁻¹‖ *
                              (‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ *
                                Real.exp
                                  (-(Cpoly *
                                    (verticalStripUpperTailDegreePolynomialKernel a b m z).re))) ≤
                            ‖A₀⁻¹‖ * K :=
                        Eq.subst
                          (motive := fun T : ℝ =>
                            ‖A₀⁻¹‖ *
                                (‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ *
                                  Real.exp
                                    (-(Cpoly *
                                      (verticalStripUpperTailDegreePolynomialKernel a b m z).re))) ≤
                              ‖A₀⁻¹‖ * T)
                          (mul_one K)
                          (mul_le_mul_of_nonneg_left hinner hscale_nonneg)
                      le_trans
                        (Eq.subst
                          (motive := fun T : ℝ => T ≤ ‖A₀⁻¹‖ * K)
                          hnorm_eq.symm
                          hscaled)
                        hscaleK_le
                  | Or.inr hzb_eq =>
                      le_trans
                        (hboundary.2 z hzb_eq.symm hz_im_ge)
                        hone_le_Ctop
              | Or.inr hza_eq =>
                  le_trans
                    (hboundary.1 z hza_eq.symm hz_im_ge)
                    hone_le_Ctop⟩

/-- Bottom-edge compact bound for the degree-polynomial bounded factor. -/
theorem verticalStripUpperTailDegreePolynomialBoundedFactor_bottomEdge_bound
    (f : ℂ → ℂ)
    (a b A C : ℝ)
    (N : ℕ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ Cbottom : ℝ,
      0 < Cbottom ∧
      ∀ z : ℂ,
        z ∈ verticalStripUpperHalfStripBottomEdge a b →
        ‖verticalStripUpperTailDegreePolynomialBoundedFactor
            f a b A C N z‖ ≤ Cbottom := by
  match IsCompact.exists_bound_of_continuousOn
      (verticalStripCompactHeightRectangle_isCompact a b)
      ((verticalStripUpperTailDegreePolynomialBoundedFactor_diffContOnCl
          f a b A C N hhol).continuousOn.mono
        (verticalStripCompactHeightRectangle_subset_closedStrip hab)) with
  | ⟨C0, hC0⟩ =>
      exact
        ⟨max C0 0 + 1,
          add_pos_of_nonneg_of_pos (le_max_right C0 0) zero_lt_one,
          fun z hz =>
            have hz_compact :
                z ∈ verticalStripCompactHeightRectangle a b :=
              verticalStripUpperHalfStripBottomEdge_subset_compactHeightRectangle hz
            have hraw :
                ‖verticalStripUpperTailDegreePolynomialBoundedFactor
                    f a b A C N z‖ ≤ C0 :=
              hC0 z hz_compact
            le_trans hraw
              (le_trans (le_max_left C0 0)
                (le_add_of_nonneg_right zero_le_one))⟩

/-- Bottom-edge compact bound for the mixed normalized factor, uniform in the
positive subcritical cosine damping parameter. -/
theorem verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_bottomEdge_bound
    (f : ℂ → ℂ)
    (a b d A C ε : ℝ)
    (N : ℕ)
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_nonneg : 0 ≤ ε)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ Cbottom : ℝ,
      0 < Cbottom ∧
      ∀ z : ℂ,
        z ∈ verticalStripUpperHalfStripBottomEdge a b →
        ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
            f a b d A C ε N z‖ ≤ Cbottom := by
  match
    verticalStripUpperTailDegreePolynomialBoundedFactor_bottomEdge_bound
      f a b A C N hab hhol
  with
  | ⟨Cbottom, hCbottom_pos, hbottom⟩ =>
      exact
        ⟨Cbottom, hCbottom_pos,
          fun z hz =>
            have hz_compact :
                z ∈ verticalStripCompactHeightRectangle a b :=
              verticalStripUpperHalfStripBottomEdge_subset_compactHeightRectangle hz
            have hza : a ≤ z.re := hz_compact.1
            have hzb : z.re ≤ b := hz_compact.2.1
            le_trans
              (verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_norm_le_degreePolynomial
                f a b d A C ε N hab hd_pos hd_threshold hε_nonneg hza hzb)
              (hbottom z hz)⟩

/-- Bounded upper half-strip control for the mixed normalized factor. -/
theorem verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_upperHalfStrip_bound
    (f : ℂ → ℂ)
    {a b c d D A₀ B₀ ε : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_pos : 0 < ε)
    (hcd : c < d)
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hD :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m)) :
    let q : ℝ :=
      sectorPowerRealConstant
        ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
    ∃ Cbound : ℝ,
      0 < Cbound ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
            f a b d A₀ (B₀ * q⁻¹) ε m z‖ ≤ Cbound := by
  let q : ℝ :=
    sectorPowerRealConstant
      ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
  let Cpoly : ℝ := B₀ * q⁻¹
  match
    verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_eventually_topEdge_bound
      f hab hd_pos hd_threshold hε_pos hcd hA₀ hB₀ hD hleft hright,
    verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_bottomEdge_bound
      f a b d A₀ Cpoly ε m hab hd_pos hd_threshold (le_of_lt hε_pos) hhol
  with
  | ⟨Ctop, hCtop_pos, htop⟩, ⟨Cbottom, hCbottom_pos, hbottom⟩ =>
      let Cbound : ℝ := max Ctop (max 1 Cbottom)
      have hCbound_pos : 0 < Cbound :=
        lt_of_lt_of_le hCtop_pos (le_max_left Ctop (max 1 Cbottom))
      have hCtop_le : Ctop ≤ Cbound :=
        le_max_left Ctop (max 1 Cbottom)
      have hone_le : (1 : ℝ) ≤ Cbound :=
        le_trans
          (le_max_left 1 Cbottom)
          (le_max_right Ctop (max 1 Cbottom))
      have hCbottom_le : Cbottom ≤ Cbound :=
        le_trans
          (le_max_right 1 Cbottom)
          (le_max_right Ctop (max 1 Cbottom))
      have hboundary :
          (∀ z : ℂ,
            z.re = a →
            1 ≤ z.im →
            ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                f a b d A₀ Cpoly ε m z‖ ≤ 1) ∧
          (∀ z : ℂ,
            z.re = b →
            1 ≤ z.im →
            ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                f a b d A₀ Cpoly ε m z‖ ≤ 1) :=
        verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_vertical_boundary_norm_le_one
          f a b d A₀ B₀ ε m hab hd_pos hd_threshold (le_of_lt hε_pos)
          hA₀ hB₀ hleft hright
      have hbottom_C :
          ∀ z : ℂ,
            z ∈ verticalStripUpperHalfStripBottomEdge a b →
            ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                f a b d A₀ Cpoly ε m z‖ ≤ Cbound :=
        fun z hz => le_trans (hbottom z hz) hCbottom_le
      have hleft_C :
          ∀ z : ℂ,
            z.re = a →
            1 ≤ z.im →
            ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                f a b d A₀ Cpoly ε m z‖ ≤ Cbound :=
        fun z hz_re hz_im =>
          le_trans (hboundary.1 z hz_re hz_im) hone_le
      have hright_C :
          ∀ z : ℂ,
            z.re = b →
            1 ≤ z.im →
            ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                f a b d A₀ Cpoly ε m z‖ ≤ Cbound :=
        fun z hz_re hz_im =>
          le_trans (hboundary.2 z hz_re hz_im) hone_le
      have htop_C :
          ∀ᶠ R : ℝ in Filter.atTop,
            ∀ z : ℂ,
              a ≤ z.re →
              z.re ≤ b →
              z.im = R →
              ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                  f a b d A₀ Cpoly ε m z‖ ≤ Cbound :=
        htop.mono
          fun R hR z hza hzb hz_im =>
            le_trans (hR z hza hzb hz_im) hCtop_le
      exact
        ⟨Cbound, hCbound_pos,
          verticalStripUpperHalfStrip_norm_le_of_eventual_top_boundary
            (verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
              f a b d A₀ Cpoly ε m)
            hab
            (verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_diffContOnCl
              f a b d A₀ Cpoly ε m hhol)
            hbottom_C hleft_C hright_C htop_C⟩

/-- Uniform bounded upper half-strip control for the mixed normalized factor.

The constant is chosen before the positive subcritical cosine damping parameter.
This is the owner-level uniformity needed for the zero-damping step. -/
theorem verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_uniform_upperHalfStrip_bound
    (f : ℂ → ℂ)
    {a b c d D A₀ B₀ : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hcd : c < d)
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hD :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m)) :
    let q : ℝ :=
      sectorPowerRealConstant
        ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
    ∃ Cbound : ℝ,
      0 < Cbound ∧
      ∀ ε : ℝ,
        0 < ε →
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          1 ≤ z.im →
          ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
              f a b d A₀ (B₀ * q⁻¹) ε m z‖ ≤ Cbound := by
  let q : ℝ :=
    sectorPowerRealConstant
      ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
  let Cpoly : ℝ := B₀ * q⁻¹
  match
    verticalStrip_finiteOrder_isBigO_eventually_topEdge_open_bound
      f hD,
    verticalStripUpperTailDegreePolynomialBoundedFactor_bottomEdge_bound
      f a b A₀ Cpoly m hab hhol
  with
  | ⟨K, hK_pos, htop_f⟩, ⟨Cbottom, hCbottom_pos, hbottom_degree⟩ =>
      let Ctop : ℝ := max (‖A₀⁻¹‖ * K) 1
      let Cbound : ℝ := max Ctop Cbottom
      have hscale_nonneg : 0 ≤ ‖A₀⁻¹‖ :=
        norm_nonneg A₀⁻¹
      have hscaleK_nonneg : 0 ≤ ‖A₀⁻¹‖ * K :=
        mul_nonneg hscale_nonneg (le_of_lt hK_pos)
      have hCtop_pos : 0 < Ctop :=
        lt_of_lt_of_le zero_lt_one (le_max_right (‖A₀⁻¹‖ * K) 1)
      have hCbound_pos : 0 < Cbound :=
        lt_of_lt_of_le hCtop_pos (le_max_left Ctop Cbottom)
      have hscaleK_le : ‖A₀⁻¹‖ * K ≤ Cbound :=
        le_trans
          (le_max_left (‖A₀⁻¹‖ * K) 1)
          (le_max_left Ctop Cbottom)
      have hone_le_Cbound : (1 : ℝ) ≤ Cbound :=
        le_trans
          (le_max_right (‖A₀⁻¹‖ * K) 1)
          (le_max_left Ctop Cbottom)
      have hCbottom_le : Cbottom ≤ Cbound :=
        le_max_right Ctop Cbottom
      have hq_pos : 0 < q :=
        finiteOrderPL_sectorPowerRealConstant_fixed_pos m
      have hqinv_nonneg : 0 ≤ q⁻¹ :=
        inv_nonneg.mpr (le_of_lt hq_pos)
      have hCpoly_nonneg : 0 ≤ Cpoly :=
        mul_nonneg (le_of_lt hB₀) hqinv_nonneg
      exact
        ⟨Cbound, hCbound_pos,
          fun ε hε_pos =>
            have hboundary :
                (∀ z : ℂ,
                  z.re = a →
                  1 ≤ z.im →
                  ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                      f a b d A₀ Cpoly ε m z‖ ≤ 1) ∧
                (∀ z : ℂ,
                  z.re = b →
                  1 ≤ z.im →
                  ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                      f a b d A₀ Cpoly ε m z‖ ≤ 1) :=
              verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_vertical_boundary_norm_le_one
                f a b d A₀ B₀ ε m hab hd_pos hd_threshold
                (le_of_lt hε_pos) hA₀ hB₀ hleft hright
            have hbottom :
                ∀ z : ℂ,
                  z ∈ verticalStripUpperHalfStripBottomEdge a b →
                  ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                      f a b d A₀ Cpoly ε m z‖ ≤ Cbound :=
              fun z hz =>
                have hz_compact :
                    z ∈ verticalStripCompactHeightRectangle a b :=
                  verticalStripUpperHalfStripBottomEdge_subset_compactHeightRectangle hz
                have hza : a ≤ z.re := hz_compact.1
                have hzb : z.re ≤ b := hz_compact.2.1
                le_trans
                  (verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_norm_le_degreePolynomial
                    f a b d A₀ Cpoly ε m hab hd_pos hd_threshold
                    (le_of_lt hε_pos) hza hzb)
                  (le_trans (hbottom_degree z hz) hCbottom_le)
            have hleft_C :
                ∀ z : ℂ,
                  z.re = a →
                  1 ≤ z.im →
                  ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                      f a b d A₀ Cpoly ε m z‖ ≤ Cbound :=
              fun z hz_re hz_im =>
                le_trans (hboundary.1 z hz_re hz_im) hone_le_Cbound
            have hright_C :
                ∀ z : ℂ,
                  z.re = b →
                  1 ≤ z.im →
                  ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                      f a b d A₀ Cpoly ε m z‖ ≤ Cbound :=
              fun z hz_re hz_im =>
                le_trans (hboundary.2 z hz_re hz_im) hone_le_Cbound
            have htop :
                ∀ᶠ R : ℝ in Filter.atTop,
                  ∀ z : ℂ,
                    a ≤ z.re →
                    z.re ≤ b →
                    z.im = R →
                    ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                        f a b d A₀ Cpoly ε m z‖ ≤ Cbound := by
              let L : ℝ := Real.cos (d * ((b - a) / 2)) / 2
              have hL_pos : 0 < L :=
                verticalStripSubcriticalCosineBarrierKernel_rightBoundary_halfCos_pos
                  hab hd_pos hd_threshold
              have habsorb :
                  ∀ᶠ R : ℝ in Filter.atTop,
                    K * Real.exp (D * Real.exp (c * R)) *
                        Real.exp (-(ε * L * Real.exp (d * R))) ≤ K :=
                doubleExponential_exp_mul_subcritical_absorber_eventually_le_const
                  hK_pos hL_pos hε_pos hcd
              have hlarge : ∀ᶠ R : ℝ in Filter.atTop, 1 ≤ R :=
                eventually_ge_atTop (1 : ℝ)
              exact
                (htop_f.and (habsorb.and hlarge)).mono
                  fun R hR z hza hzb hz_im =>
                    have hz_im_ge : 1 ≤ z.im :=
                      Eq.subst
                        (motive := fun T : ℝ => 1 ≤ T)
                        hz_im.symm
                        hR.2.2
                    match lt_or_eq_of_le hza with
                    | Or.inl hza_strict =>
                        match lt_or_eq_of_le hzb with
                        | Or.inl hzb_strict =>
                            have hf :
                                ‖f z‖ ≤
                                  K * Real.exp (D * Real.exp (c * z.im)) := by
                              have hraw :
                                  ‖f z‖ ≤
                                    K * Real.exp (D * Real.exp (c * R)) :=
                                hR.1 z hza_strict hzb_strict hz_im
                              have hrhs :
                                  K * Real.exp (D * Real.exp (c * R)) =
                                    K * Real.exp (D * Real.exp (c * z.im)) :=
                                congrArg
                                  (fun y : ℝ =>
                                    K * Real.exp (D * Real.exp (c * y)))
                                  hz_im.symm
                              Eq.subst
                                (motive := fun x : ℝ => ‖f z‖ ≤ x)
                                hrhs
                                hraw
                            have hpre :
                                ‖verticalStripSubcriticalCosineDampedFamily
                                    f a b d ε z‖ ≤
                                  (K * Real.exp (D * Real.exp (c * z.im))) *
                                    Real.exp
                                      (-(ε *
                                          (Real.cos (d * ((b - a) / 2)) / 2) *
                                        Real.exp (d * z.im))) :=
                              verticalStripSubcriticalCosineDampedFamily_topEdge_preAbsorption
                                f hab hd_pos hd_threshold (le_of_lt hε_pos)
                                (le_of_lt hza_strict) (le_of_lt hzb_strict) hf
                            have htarget :
                                (K * Real.exp (D * Real.exp (c * z.im))) *
                                    Real.exp
                                      (-(ε *
                                          (Real.cos (d * ((b - a) / 2)) / 2) *
                                        Real.exp (d * z.im))) =
                                  K * Real.exp (D * Real.exp (c * R)) *
                                    Real.exp (-(ε * L * Real.exp (d * R))) := by
                              calc
                                (K * Real.exp (D * Real.exp (c * z.im))) *
                                    Real.exp
                                      (-(ε *
                                          (Real.cos (d * ((b - a) / 2)) / 2) *
                                        Real.exp (d * z.im))) =
                                  K * Real.exp (D * Real.exp (c * R)) *
                                    Real.exp
                                      (-(ε *
                                          (Real.cos (d * ((b - a) / 2)) / 2) *
                                        Real.exp (d * R))) := by
                                    exact congrArg₂
                                      (fun x y : ℝ =>
                                        K * Real.exp (D * Real.exp (c * x)) *
                                          Real.exp
                                            (-(ε *
                                                (Real.cos
                                                    (d * ((b - a) / 2)) / 2) *
                                              Real.exp (d * y))))
                                      hz_im hz_im
                                _ =
                                  K * Real.exp (D * Real.exp (c * R)) *
                                    Real.exp (-(ε * L * Real.exp (d * R))) := rfl
                            have hdamped :
                                ‖verticalStripSubcriticalCosineDampedFamily
                                    f a b d ε z‖ ≤ K :=
                              le_trans hpre
                                (Eq.subst
                                  (motive := fun x : ℝ => x ≤ K)
                                  htarget.symm
                                  hR.2.1)
                            have hnorm_eq :
                                ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                                    f a b d A₀ Cpoly ε m z‖ =
                                  ‖A₀⁻¹‖ *
                                    (‖verticalStripSubcriticalCosineDampedFamily
                                        f a b d ε z‖ *
                                      Real.exp
                                        (-(Cpoly *
                                          (verticalStripUpperTailDegreePolynomialKernel
                                            a b m z).re))) :=
                              verticalStripUpperTailDegreePolynomialBoundedFactor_norm_eq
                                (verticalStripSubcriticalCosineDampedFamily
                                  f a b d ε)
                                a b A₀ Cpoly m z
                            have hexp_le :
                                Real.exp
                                    (-(Cpoly *
                                      (verticalStripUpperTailDegreePolynomialKernel
                                        a b m z).re)) ≤ 1 :=
                              verticalStripUpperTailDegreePolynomial_exp_le_one_on_upperTail
                                a b Cpoly m hza hzb hz_im_ge hCpoly_nonneg
                            have hinner :
                                ‖verticalStripSubcriticalCosineDampedFamily
                                    f a b d ε z‖ *
                                    Real.exp
                                      (-(Cpoly *
                                        (verticalStripUpperTailDegreePolynomialKernel
                                          a b m z).re)) ≤
                                  K * 1 :=
                              mul_le_mul hdamped hexp_le
                                (le_of_lt
                                  (Real.exp_pos
                                    (-(Cpoly *
                                      (verticalStripUpperTailDegreePolynomialKernel
                                        a b m z).re))))
                                (norm_nonneg
                                  (verticalStripSubcriticalCosineDampedFamily
                                    f a b d ε z))
                            have hscaled :
                                ‖A₀⁻¹‖ *
                                    (‖verticalStripSubcriticalCosineDampedFamily
                                        f a b d ε z‖ *
                                      Real.exp
                                        (-(Cpoly *
                                          (verticalStripUpperTailDegreePolynomialKernel
                                            a b m z).re))) ≤
                                  ‖A₀⁻¹‖ * K :=
                              Eq.subst
                                (motive := fun T : ℝ =>
                                  ‖A₀⁻¹‖ *
                                      (‖verticalStripSubcriticalCosineDampedFamily
                                          f a b d ε z‖ *
                                        Real.exp
                                          (-(Cpoly *
                                            (verticalStripUpperTailDegreePolynomialKernel
                                              a b m z).re))) ≤
                                    ‖A₀⁻¹‖ * T)
                                (mul_one K)
                                (mul_le_mul_of_nonneg_left hinner hscale_nonneg)
                            le_trans
                              (Eq.subst
                                (motive := fun T : ℝ => T ≤ ‖A₀⁻¹‖ * K)
                                hnorm_eq.symm
                                hscaled)
                              hscaleK_le
                        | Or.inr hzb_eq =>
                            le_trans
                              (hboundary.2 z hzb_eq.symm hz_im_ge)
                              hone_le_Cbound
                    | Or.inr hza_eq =>
                        le_trans
                          (hboundary.1 z hza_eq.symm hz_im_ge)
                          hone_le_Cbound
            verticalStripUpperHalfStrip_norm_le_of_eventual_top_boundary
              (verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
                f a b d A₀ Cpoly ε m)
              hab
              (verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_diffContOnCl
                f a b d A₀ Cpoly ε m hhol)
              hbottom hleft_C hright_C htop⟩

/-- The mixed cosine/degree-polynomial normalized factor tends to the pure
degree-polynomial normalized factor as the positive cosine damping parameter
tends to zero. -/
theorem verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_norm_tendsto_zeroDamping
    (f : ℂ → ℂ)
    (a b d A C : ℝ)
    (N : ℕ)
    (z : ℂ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
            f a b d A C ε N z‖)
      (𝓝[>] (0 : ℝ))
      (𝓝
        ‖verticalStripUpperTailDegreePolynomialBoundedFactor
            f a b A C N z‖) := by
  let K : ℂ := verticalStripUpperTailDegreePolynomialKernel a b N z
  let E : ℂ := Complex.exp (-((C : ℝ) : ℂ) * K)
  have hdamped :
      Filter.Tendsto
        (fun ε : ℝ => verticalStripSubcriticalCosineDampedFamily f a b d ε z)
        (𝓝[>] (0 : ℝ))
        (𝓝 (f z)) :=
    verticalStripSubcriticalCosineDampedFamily_tendsto_zeroDamping f a b d z
  have hmul :
      Filter.Tendsto
        (fun ε : ℝ =>
          ((A⁻¹ : ℝ) : ℂ) *
            (verticalStripSubcriticalCosineDampedFamily f a b d ε z * E))
        (𝓝[>] (0 : ℝ))
        (𝓝 (((A⁻¹ : ℝ) : ℂ) * (f z * E))) :=
    tendsto_const_nhds.mul (hdamped.mul tendsto_const_nhds)
  have hleft_eq :
      (fun ε : ℝ =>
        ((A⁻¹ : ℝ) : ℂ) *
          (verticalStripSubcriticalCosineDampedFamily f a b d ε z * E)) =
      fun ε : ℝ =>
        verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
          f a b d A C ε N z := by
    funext ε
    rfl
  have hright_eq :
      ((A⁻¹ : ℝ) : ℂ) * (f z * E) =
        verticalStripUpperTailDegreePolynomialBoundedFactor f a b A C N z := by
    rfl
  have hcomplex :
      Filter.Tendsto
        (fun ε : ℝ =>
          verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
            f a b d A C ε N z)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (verticalStripUpperTailDegreePolynomialBoundedFactor
            f a b A C N z)) :=
    Eq.subst
      (motive := fun lhs : ℝ → ℂ =>
        Filter.Tendsto lhs (𝓝[>] (0 : ℝ))
          (𝓝
            (verticalStripUpperTailDegreePolynomialBoundedFactor
              f a b A C N z)))
      hleft_eq
      (Eq.subst
        (motive := fun rhs : ℂ =>
          Filter.Tendsto
            (fun ε : ℝ =>
              ((A⁻¹ : ℝ) : ℂ) *
                (verticalStripSubcriticalCosineDampedFamily f a b d ε z * E))
            (𝓝[>] (0 : ℝ))
            (𝓝 rhs))
        hright_eq
        hmul)
  exact hcomplex.norm

/-- A uniform mixed cosine/degree-polynomial normalized bound passes to the
pure degree-polynomial normalized factor as the damping parameter tends to
zero. -/
theorem verticalStripUpperTailDegreePolynomialBoundedFactor_bound_of_uniform_mixed_bound
    (f : ℂ → ℂ)
    (a b d A C : ℝ)
    (N : ℕ)
    (z : ℂ)
    {M : ℝ}
    (hmixed :
      ∀ ε : ℝ,
        0 < ε →
        ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
            f a b d A C ε N z‖ ≤ M) :
    ‖verticalStripUpperTailDegreePolynomialBoundedFactor
        f a b A C N z‖ ≤ M := by
  exact
    real_norm_bound_of_tendsto_from_positive_side
      (verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_norm_tendsto_zeroDamping
        f a b d A C N z)
      hmixed

/-- A bounded degree-polynomial normalized factor undamps to a finite envelope
after increasing the leading constant by the normalized bound. -/
theorem verticalStripUpperTailDegreePolynomialBoundedFactor_undamps_to_finiteEnvelope_of_bound
    (f : ℂ → ℂ)
    (a b A B C M : ℝ)
    (m N : ℕ)
    (z : ℂ)
    (hA : 0 < A)
    (hM : 0 < M)
    (hbound :
      ‖verticalStripUpperTailDegreePolynomialBoundedFactor
          f a b A C N z‖ ≤ M)
    (hupper :
      C * (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤
        B * (1 + ‖z‖) ^ m) :
    ‖f z‖ ≤ (A * M) * Real.exp (B * (1 + ‖z‖) ^ m) := by
  let X : ℝ :=
    C * (verticalStripUpperTailDegreePolynomialKernel a b N z).re
  have hfactor_norm :
      ‖verticalStripUpperTailDegreePolynomialBoundedFactor f a b A C N z‖ =
        ‖A⁻¹‖ * (‖f z‖ * Real.exp (-X)) :=
    verticalStripUpperTailDegreePolynomialBoundedFactor_norm_eq f a b A C N z
  have hAinv_nonneg : 0 ≤ A⁻¹ :=
    inv_nonneg.mpr (le_of_lt hA)
  have hAinv_norm : ‖A⁻¹‖ = A⁻¹ :=
    Real.norm_of_nonneg hAinv_nonneg
  have hunit_real :
      A⁻¹ * Real.exp (-X) * ‖f z‖ ≤ M := by
    have hrewrite :
        A⁻¹ * Real.exp (-X) * ‖f z‖ =
          ‖A⁻¹‖ * (‖f z‖ * Real.exp (-X)) := by
      calc
        A⁻¹ * Real.exp (-X) * ‖f z‖ =
            A⁻¹ * (Real.exp (-X) * ‖f z‖) :=
          mul_assoc A⁻¹ (Real.exp (-X)) ‖f z‖
        _ = A⁻¹ * (‖f z‖ * Real.exp (-X)) :=
          congrArg (fun y : ℝ => A⁻¹ * y)
            (mul_comm (Real.exp (-X)) ‖f z‖)
        _ = ‖A⁻¹‖ * (‖f z‖ * Real.exp (-X)) :=
          congrArg (fun y : ℝ => y * (‖f z‖ * Real.exp (-X)))
            hAinv_norm.symm
    Eq.subst
      (motive := fun T : ℝ => T ≤ M)
      hrewrite.symm
      (Eq.subst
        (motive := fun T : ℝ => T ≤ M)
        hfactor_norm
        hbound)
  have hM_inv_nonneg : 0 ≤ M⁻¹ :=
    inv_nonneg.mpr (le_of_lt hM)
  have hunit_scaled :
      (A * M)⁻¹ * Real.exp (-X) * ‖f z‖ ≤ 1 := by
    have hcollapse :
        (A * M)⁻¹ * Real.exp (-X) * ‖f z‖ =
          M⁻¹ * (A⁻¹ * Real.exp (-X) * ‖f z‖) := by
      have hAM_inv :
          (A * M)⁻¹ = M⁻¹ * A⁻¹ :=
        mul_inv_rev A M
      calc
        (A * M)⁻¹ * Real.exp (-X) * ‖f z‖ =
            (M⁻¹ * A⁻¹) * Real.exp (-X) * ‖f z‖ :=
          congrArg (fun y : ℝ => y * Real.exp (-X) * ‖f z‖) hAM_inv
        _ = M⁻¹ * (A⁻¹ * Real.exp (-X) * ‖f z‖) := by
          calc
            (M⁻¹ * A⁻¹) * Real.exp (-X) * ‖f z‖ =
                M⁻¹ * (A⁻¹ * Real.exp (-X)) * ‖f z‖ :=
              congrArg (fun y : ℝ => y * ‖f z‖)
                (mul_assoc M⁻¹ A⁻¹ (Real.exp (-X)))
            _ = M⁻¹ * (A⁻¹ * Real.exp (-X) * ‖f z‖) :=
              mul_assoc M⁻¹ (A⁻¹ * Real.exp (-X)) ‖f z‖
    have hscaled :
        M⁻¹ * (A⁻¹ * Real.exp (-X) * ‖f z‖) ≤ M⁻¹ * M :=
      mul_le_mul_of_nonneg_left hunit_real hM_inv_nonneg
    have hright : M⁻¹ * M = 1 :=
      inv_mul_cancel₀ hM.ne'
    Eq.subst
      (motive := fun T : ℝ => T ≤ 1)
      hcollapse
      (Eq.subst
        (motive := fun T : ℝ =>
          M⁻¹ * (A⁻¹ * Real.exp (-X) * ‖f z‖) ≤ T)
        hright
        hscaled)
  have hAM_pos : 0 < A * M :=
    mul_pos hA hM
  have hraw :
      ‖f z‖ ≤ (A * M) * Real.exp X :=
    by
      let E : ℝ := Real.exp X
      let En : ℝ := Real.exp (-X)
      let S : ℝ := (A * M) * E
      let Cscale : ℝ := (A * M)⁻¹ * En
      have hS_pos : 0 < S :=
        mul_pos hAM_pos (Real.exp_pos X)
      have hC_mul_S : Cscale * S = 1 := by
        have hcollapse : En * S = A * M := by
          exact exp_negative_growth_mul_growth_cancel (A * M) X
        calc
          Cscale * S = ((A * M)⁻¹ * En) * S := rfl
          _ = (A * M)⁻¹ * (En * S) :=
            mul_assoc (A * M)⁻¹ En S
          _ = (A * M)⁻¹ * (A * M) :=
            congrArg (fun y : ℝ => (A * M)⁻¹ * y) hcollapse
          _ = 1 := inv_mul_cancel₀ hAM_pos.ne'
      have hscaled :
          (Cscale * ‖f z‖) * S ≤ 1 * S :=
        mul_le_mul_of_nonneg_right hunit_scaled (le_of_lt hS_pos)
      have hleft :
          (Cscale * ‖f z‖) * S = ‖f z‖ := by
        calc
          (Cscale * ‖f z‖) * S =
              Cscale * (‖f z‖ * S) := mul_assoc Cscale ‖f z‖ S
          _ = Cscale * (S * ‖f z‖) :=
            congrArg (fun y : ℝ => Cscale * y) (mul_comm ‖f z‖ S)
          _ = (Cscale * S) * ‖f z‖ :=
            (mul_assoc Cscale S ‖f z‖).symm
          _ = 1 * ‖f z‖ :=
            congrArg (fun y : ℝ => y * ‖f z‖) hC_mul_S
          _ = ‖f z‖ := one_mul ‖f z‖
      have hright : 1 * S = S :=
        one_mul S
      exact
        Eq.subst
          (motive := fun lhs : ℝ => lhs ≤ S)
          hleft
          (Eq.subst
            (motive := fun rhs : ℝ => (Cscale * ‖f z‖) * S ≤ rhs)
            hright
            hscaled)
  have hexp_le :
      Real.exp X ≤ Real.exp (B * (1 + ‖z‖) ^ m) :=
    Real.exp_le_exp.mpr hupper
  have hAM_nonneg : 0 ≤ A * M :=
    le_of_lt hAM_pos
  exact
    le_trans hraw
      (mul_le_mul_of_nonneg_left hexp_le hAM_nonneg)

/-- Uniform half-strip control for all positive mixed dampings gives uniform
control of the pure degree-polynomial normalized factor. -/
theorem verticalStripUpperTailDegreePolynomialBoundedFactor_bound_from_uniform_mixed_upperHalfStrip
    (f : ℂ → ℂ)
    {a b c d D A₀ B₀ : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hcd : c < d)
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hD :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m)) :
    let q : ℝ :=
      sectorPowerRealConstant
        ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
    ∃ Cbound : ℝ,
      0 < Cbound ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖verticalStripUpperTailDegreePolynomialBoundedFactor
            f a b A₀ (B₀ * q⁻¹) m z‖ ≤ Cbound := by
  let q : ℝ :=
    sectorPowerRealConstant
      ((2 * ((m + 1 : ℕ) : ℝ))⁻¹) m
  match
    verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_uniform_upperHalfStrip_bound
      f hab hd_pos hd_threshold hcd hA₀ hB₀ hhol hD hleft hright
  with
  | ⟨Cbound, hCbound_pos, huniform⟩ =>
      exact
        ⟨Cbound, hCbound_pos,
          fun z hza hzb hzim =>
            verticalStripUpperTailDegreePolynomialBoundedFactor_bound_of_uniform_mixed_bound
              f a b d A₀ (B₀ * q⁻¹) m z
              (fun ε hε =>
                huniform ε hε z hza hzb hzim)⟩

/-- Upper-tail finite-order Phragmen-Lindelöf theorem with polynomial-exponential
vertical boundary growth.

This is the remaining analytic owner sink for C4.  It is the true theorem
needed here: subcritical interior growth and finite-order control on both
vertical boundary rays propagate a finite-order envelope to the upper closed
half-strip.  It is not a bounded-boundary statement, and it cannot be supplied
by choosing a fake normalizer or by dividing by a non-holomorphic real-valued
envelope. -/
theorem strip_finite_order_growth_upperTail_finiteOrderPL_ownerGap
    (f : ℂ → ℂ)
    (a b A₀ B₀ : ℝ)
    (m₀ : ℕ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hfinite with
  | ⟨c, hc_threshold, D, hD⟩ =>
      have hwidth_pos : 0 < b - a :=
        sub_pos.mpr hab
      have hstrip_threshold_pos : 0 < π / (b - a) :=
        div_pos Real.pi_pos hwidth_pos
      have hmax_lt_threshold : max c 0 < π / (b - a) :=
        max_lt hc_threshold hstrip_threshold_pos
      match exists_between hmax_lt_threshold with
      | ⟨d, hd_gt_max, hd_threshold⟩ =>
          have hd_pos : 0 < d :=
            lt_of_le_of_lt (le_max_right c 0) hd_gt_max
          have hcd : c < d :=
            lt_of_le_of_lt (le_max_left c 0) hd_gt_max
          let q : ℝ :=
            sectorPowerRealConstant
              ((2 * ((m₀ + 1 : ℕ) : ℝ))⁻¹) m₀
          let Cpoly : ℝ := B₀ * q⁻¹
          have hCpoly_pos : 0 < Cpoly :=
            finiteOrderPL_degreePolynomialBoundaryCoefficient_pos B₀ m₀ hB₀
          have hCpoly_nonneg : 0 ≤ Cpoly :=
            le_of_lt hCpoly_pos
          match
            verticalStripUpperTailDegreePolynomialBoundedFactor_bound_from_uniform_mixed_upperHalfStrip
              f hab hd_pos hd_threshold hcd hA₀ hB₀ hhol hD hleft hright
          with
          | ⟨M, hM_pos, hM_bound⟩ =>
              match
                verticalStripUpperTailDegreePolynomialKernel_re_le_one_add_norm_envelope
                  a b Cpoly m₀ hCpoly_nonneg
              with
              | ⟨Bgeom, hBgeom_pos, hkernel_envelope⟩ =>
                  exact
                    ⟨A₀ * M, Bgeom, m₀,
                      mul_pos hA₀ hM_pos,
                      hBgeom_pos,
                      fun z hza hzb hzim =>
                        verticalStripUpperTailDegreePolynomialBoundedFactor_undamps_to_finiteEnvelope_of_bound
                          f a b A₀ Bgeom Cpoly M m₀ m₀ z hA₀ hM_pos
                          (hM_bound z hza hzb hzim)
                          (hkernel_envelope z hza hzb hzim)⟩

/-- If the normalizing factor has norm at most one, the normalized finite-order
envelope is bounded by the original finite-order envelope. -/
theorem finiteOrderEnvelope_mul_norm_le_self_of_norm_le_one
    (A B : ℝ)
    (m : ℕ)
    (z : ℂ)
    (hA : 0 < A)
    (g : ℂ → ℂ)
    (hg : ‖g z‖ ≤ 1) :
    A * Real.exp (B * (1 + ‖z‖) ^ m) * ‖g z‖ ≤
      A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  have hscale_nonneg :
      0 ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    mul_nonneg (le_of_lt hA)
      (le_of_lt (Real.exp_pos (B * (1 + ‖z‖) ^ m)))
  have hscaled :
      A * Real.exp (B * (1 + ‖z‖) ^ m) * ‖g z‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m) * 1 :=
    mul_le_mul_of_nonneg_left hg hscale_nonneg
  have hright_one :
      A * Real.exp (B * (1 + ‖z‖) ^ m) * 1 =
        A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    mul_one (A * Real.exp (B * (1 + ‖z‖) ^ m))
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        A * Real.exp (B * (1 + ‖z‖) ^ m) * ‖g z‖ ≤ x)
      hright_one
      hscaled

/-- A positive exponential times a sufficiently strong negative exponential is
bounded by one. -/
theorem real_exp_mul_exp_neg_le_one_of_le
    {X Y : ℝ}
    (hXY : X ≤ Y) :
    Real.exp X * Real.exp (-Y) ≤ 1 := by
  have hsum_nonpos : X + -Y ≤ 0 := by
    calc
      X + -Y ≤ Y + -Y := add_le_add_right hXY (-Y)
      _ = 0 := add_neg_cancel Y
  have hprod_eq :
      Real.exp X * Real.exp (-Y) = Real.exp (X + -Y) :=
    (Real.exp_add X (-Y)).symm
  exact
    Eq.subst
      (motive := fun T : ℝ => T ≤ 1)
      hprod_eq.symm
      (Real.exp_le_one_iff.mpr hsum_nonpos)

/-- A polynomial-normalized factor whose unscaled norm is bounded by the
boundary constant has unit norm after multiplying by `A⁻¹`. -/
theorem verticalStripUpperTailPolynomialBoundedFactor_norm_le_one_of_normalized_norm_le
    (f : ℂ → ℂ)
    (a b A C : ℝ)
    (N : ℕ)
    (z : ℂ)
    (hA : 0 < A)
    (hnormalized :
      ‖verticalStripUpperTailPolynomialNormalizedFamily f a b C N z‖ ≤ A) :
    ‖verticalStripUpperTailPolynomialBoundedFactor f a b A C N z‖ ≤ 1 := by
  let F : ℂ :=
    verticalStripUpperTailPolynomialNormalizedFamily f a b C N z
  have hA_nonneg : 0 ≤ A :=
    le_of_lt hA
  have hAinv_nonneg : 0 ≤ A⁻¹ :=
    inv_nonneg.mpr hA_nonneg
  have hAinv_norm : ‖A⁻¹‖ = A⁻¹ :=
    Real.norm_of_nonneg hAinv_nonneg
  have hcoe_norm : ‖((A⁻¹ : ℝ) : ℂ)‖ = ‖A⁻¹‖ :=
    RCLike.norm_ofReal (K := ℂ) (A⁻¹)
  have hcoe_nonneg : 0 ≤ ‖((A⁻¹ : ℝ) : ℂ)‖ :=
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      hcoe_norm.symm
      (norm_nonneg (A⁻¹))
  have hscaled :
      ‖((A⁻¹ : ℝ) : ℂ)‖ * ‖F‖ ≤ ‖A⁻¹‖ * A :=
    le_trans
      (mul_le_mul_of_nonneg_left hnormalized hcoe_nonneg)
      (le_of_eq (congrArg (fun x : ℝ => x * A) hcoe_norm))
  have hcollapse : ‖A⁻¹‖ * A = 1 := by
    calc
      ‖A⁻¹‖ * A = A⁻¹ * A :=
        congrArg (fun x : ℝ => x * A) hAinv_norm
      _ = 1 := inv_mul_cancel₀ hA.ne'
  have hnorm_eq :
      ‖verticalStripUpperTailPolynomialBoundedFactor f a b A C N z‖ =
        ‖((A⁻¹ : ℝ) : ℂ)‖ * ‖F‖ := by
    calc
      ‖verticalStripUpperTailPolynomialBoundedFactor f a b A C N z‖ =
          ‖((A⁻¹ : ℝ) : ℂ) * F‖ := rfl
      _ = ‖((A⁻¹ : ℝ) : ℂ)‖ * ‖F‖ :=
        norm_mul (((A⁻¹ : ℝ) : ℂ)) F
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        ‖verticalStripUpperTailPolynomialBoundedFactor f a b A C N z‖ ≤ x)
      hcollapse
      (Eq.subst
        (motive := fun x : ℝ => x ≤ ‖A⁻¹‖ * A)
        hnorm_eq.symm
        hscaled)

/-- Boundary finite-order control plus real-part dominance of the holomorphic
polynomial normalizer gives unit control of the bounded normalized factor. -/
theorem verticalStripUpperTailPolynomialBoundedFactor_boundary_norm_le_one_of_re_dominates
    (f : ℂ → ℂ)
    (a b A B C : ℝ)
    (m N : ℕ)
    (z : ℂ)
    (hA : 0 < A)
    (hboundary :
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))
    (hdominates :
      B * (1 + ‖z.im‖) ^ m ≤
        C * (verticalStripUpperTailPolynomialNormalizerKernel a b N z).re) :
    ‖verticalStripUpperTailPolynomialBoundedFactor f a b A C N z‖ ≤ 1 := by
  let X : ℝ := B * (1 + ‖z.im‖) ^ m
  let Y : ℝ :=
    C * (verticalStripUpperTailPolynomialNormalizerKernel a b N z).re
  have hnorm_eq :
      ‖verticalStripUpperTailPolynomialNormalizedFamily f a b C N z‖ =
        ‖f z‖ * Real.exp (-Y) :=
    verticalStripUpperTailPolynomialNormalizedFamily_norm_eq f a b C N z
  have hboundaryY :
      ‖f z‖ * Real.exp (-Y) ≤
        (A * Real.exp X) * Real.exp (-Y) :=
    mul_le_mul_of_nonneg_right hboundary
      (le_of_lt (Real.exp_pos (-Y)))
  have hcollapse :
      (A * Real.exp X) * Real.exp (-Y) ≤ A := by
    have hmul :
        Real.exp X * Real.exp (-Y) ≤ 1 :=
      real_exp_mul_exp_neg_le_one_of_le hdominates
    have hnonneg_A : 0 ≤ A :=
      le_of_lt hA
    have hassoc :
        (A * Real.exp X) * Real.exp (-Y) =
          A * (Real.exp X * Real.exp (-Y)) :=
      mul_assoc A (Real.exp X) (Real.exp (-Y))
    calc
      (A * Real.exp X) * Real.exp (-Y) =
          A * (Real.exp X * Real.exp (-Y)) := hassoc
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hmul hnonneg_A
      _ = A := mul_one A
  have hnormalized :
      ‖verticalStripUpperTailPolynomialNormalizedFamily f a b C N z‖ ≤ A :=
    Eq.subst
      (motive := fun T : ℝ => T ≤ A)
      hnorm_eq.symm
      (le_trans hboundaryY hcollapse)
  exact
    verticalStripUpperTailPolynomialBoundedFactor_norm_le_one_of_normalized_norm_le
      f a b A C N z hA hnormalized

/-- Boundary finite-order control plus real-part dominance of the
degree-dependent polynomial normalizer gives unit boundary control. -/
theorem verticalStripUpperTailDegreePolynomialBoundedFactor_boundary_norm_le_one_of_re_dominates
    (f : ℂ → ℂ)
    (a b A B C : ℝ)
    (m N : ℕ)
    (z : ℂ)
    (hA : 0 < A)
    (hboundary :
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))
    (hdominates :
      B * (1 + ‖z.im‖) ^ m ≤
        C * (verticalStripUpperTailDegreePolynomialKernel a b N z).re) :
    ‖verticalStripUpperTailDegreePolynomialBoundedFactor f a b A C N z‖ ≤ 1 := by
  let X : ℝ := B * (1 + ‖z.im‖) ^ m
  let Y : ℝ :=
    C * (verticalStripUpperTailDegreePolynomialKernel a b N z).re
  have hnorm_eq :
      ‖verticalStripUpperTailDegreePolynomialBoundedFactor f a b A C N z‖ =
        ‖A⁻¹‖ * (‖f z‖ * Real.exp (-Y)) :=
    verticalStripUpperTailDegreePolynomialBoundedFactor_norm_eq f a b A C N z
  have hAinv_nonneg : 0 ≤ A⁻¹ :=
    inv_nonneg.mpr (le_of_lt hA)
  have hAinv_norm : ‖A⁻¹‖ = A⁻¹ :=
    Real.norm_of_nonneg hAinv_nonneg
  have hunit_real :
      A⁻¹ * Real.exp (-Y) * ‖f z‖ ≤ 1 := by
    have hboundaryY :
        ‖f z‖ * Real.exp (-Y) ≤
          (A * Real.exp X) * Real.exp (-Y) :=
      mul_le_mul_of_nonneg_right hboundary
        (le_of_lt (Real.exp_pos (-Y)))
    have hcollapse :
        (A * Real.exp X) * Real.exp (-Y) ≤ A := by
      have hmul :
          Real.exp X * Real.exp (-Y) ≤ 1 :=
        real_exp_mul_exp_neg_le_one_of_le hdominates
      have hnonneg_A : 0 ≤ A :=
        le_of_lt hA
      have hassoc :
          (A * Real.exp X) * Real.exp (-Y) =
            A * (Real.exp X * Real.exp (-Y)) :=
        mul_assoc A (Real.exp X) (Real.exp (-Y))
      calc
        (A * Real.exp X) * Real.exp (-Y) =
            A * (Real.exp X * Real.exp (-Y)) := hassoc
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hmul hnonneg_A
        _ = A := mul_one A
    have hscaled :
        A⁻¹ * (‖f z‖ * Real.exp (-Y)) ≤ A⁻¹ * A :=
      mul_le_mul_of_nonneg_left (le_trans hboundaryY hcollapse) hAinv_nonneg
    have hleft :
        A⁻¹ * (‖f z‖ * Real.exp (-Y)) =
          A⁻¹ * Real.exp (-Y) * ‖f z‖ := by
      calc
        A⁻¹ * (‖f z‖ * Real.exp (-Y)) =
            A⁻¹ * (Real.exp (-Y) * ‖f z‖) :=
          congrArg (fun t : ℝ => A⁻¹ * t)
            (mul_comm ‖f z‖ (Real.exp (-Y)))
        _ = A⁻¹ * Real.exp (-Y) * ‖f z‖ :=
          (mul_assoc A⁻¹ (Real.exp (-Y)) ‖f z‖).symm
    have hright : A⁻¹ * A = 1 :=
      inv_mul_cancel₀ hA.ne'
    Eq.subst
      (motive := fun lhs : ℝ => lhs ≤ 1)
      hleft
      (Eq.subst
        (motive := fun rhs : ℝ =>
          A⁻¹ * (‖f z‖ * Real.exp (-Y)) ≤ rhs)
        hright
        hscaled)
  have hnorm_real :
      ‖verticalStripUpperTailDegreePolynomialBoundedFactor f a b A C N z‖ =
        A⁻¹ * Real.exp (-Y) * ‖f z‖ := by
    have hrewrite :
        ‖A⁻¹‖ * (‖f z‖ * Real.exp (-Y)) =
          A⁻¹ * Real.exp (-Y) * ‖f z‖ := by
      calc
        ‖A⁻¹‖ * (‖f z‖ * Real.exp (-Y)) =
            A⁻¹ * (‖f z‖ * Real.exp (-Y)) :=
          congrArg (fun t : ℝ => t * (‖f z‖ * Real.exp (-Y)))
            hAinv_norm
        _ = A⁻¹ * (Real.exp (-Y) * ‖f z‖) :=
          congrArg (fun t : ℝ => A⁻¹ * t)
            (mul_comm ‖f z‖ (Real.exp (-Y)))
        _ = A⁻¹ * Real.exp (-Y) * ‖f z‖ :=
          (mul_assoc A⁻¹ (Real.exp (-Y)) ‖f z‖).symm
    Eq.trans hnorm_eq hrewrite
  exact
    Eq.subst
      (motive := fun T : ℝ => T ≤ 1)
      hnorm_real.symm
      hunit_real

/-- For the mixed subcritical-cosine/degree-polynomial factor, the cosine
damping can only reduce the boundary norm on the closed strip, so the same
polynomial real-part dominance gives unit boundary control. -/
theorem verticalStripSubcriticalCosineDegreePolynomialBoundedFactor_boundary_norm_le_one_of_re_dominates
    (f : ℂ → ℂ)
    (a b d A B C ε : ℝ)
    (m N : ℕ)
    (z : ℂ)
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hA : 0 < A)
    (hboundary :
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))
    (hdominates :
      B * (1 + ‖z.im‖) ^ m ≤
        C * (verticalStripUpperTailDegreePolynomialKernel a b N z).re) :
    ‖verticalStripSubcriticalCosineDegreePolynomialBoundedFactor
        f a b d A C ε N z‖ ≤ 1 := by
  have hdamped_boundary :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
        A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
    le_trans
      (verticalStripSubcriticalCosineDampedFamily_norm_le_original_on_closedStrip
        f hab hd_pos hd_threshold hε z hza hzb)
      hboundary
  exact
    verticalStripUpperTailDegreePolynomialBoundedFactor_boundary_norm_le_one_of_re_dominates
      (verticalStripSubcriticalCosineDampedFamily f a b d ε)
      a b A B C m N z hA hdamped_boundary hdominates

/-- Undo a positive real exponential normalization with an arbitrary real
exponent. -/
theorem real_bound_of_scaled_exp_neg_unit
    {A X x : ℝ}
    (hA : 0 < A)
    (hunit : A⁻¹ * Real.exp (-X) * x ≤ 1) :
    x ≤ A * Real.exp X := by
  let E : ℝ := Real.exp X
  let En : ℝ := Real.exp (-X)
  let S : ℝ := A * E
  let C : ℝ := A⁻¹ * En
  have hS_pos : 0 < S :=
    mul_pos hA (Real.exp_pos X)
  have hC_mul_S : C * S = 1 := by
    have hcollapse : En * S = A := by
      exact exp_negative_growth_mul_growth_cancel A X
    calc
      C * S = (A⁻¹ * En) * S := rfl
      _ = A⁻¹ * (En * S) := mul_assoc A⁻¹ En S
      _ = A⁻¹ * A := congrArg (fun y : ℝ => A⁻¹ * y) hcollapse
      _ = 1 := inv_mul_cancel₀ hA.ne'
  have hscaled :
      (C * x) * S ≤ 1 * S :=
    mul_le_mul_of_nonneg_right hunit (le_of_lt hS_pos)
  have hleft :
      (C * x) * S = x := by
    calc
      (C * x) * S = C * (x * S) := mul_assoc C x S
      _ = C * (S * x) := congrArg (fun y : ℝ => C * y) (mul_comm x S)
      _ = (C * S) * x := (mul_assoc C S x).symm
      _ = 1 * x := congrArg (fun y : ℝ => y * x) hC_mul_S
      _ = x := one_mul x
  have hright : 1 * S = S :=
    one_mul S
  exact
    Eq.subst
      (motive := fun lhs : ℝ => lhs ≤ S)
      hleft
      (Eq.subst
        (motive := fun rhs : ℝ => (C * x) * S ≤ rhs)
        hright
        hscaled)

/-- A unit bound for the constructed polynomial bounded factor undamps to the
finite envelope once the real part of the polynomial normalizer is bounded
above by that envelope exponent. -/
theorem verticalStripUpperTailPolynomialBoundedFactor_undamps_to_finiteEnvelope
    (f : ℂ → ℂ)
    (a b A B C : ℝ)
    (m N : ℕ)
    (z : ℂ)
    (hA : 0 < A)
    (hunit :
      ‖verticalStripUpperTailPolynomialBoundedFactor f a b A C N z‖ ≤ 1)
    (hupper :
      C * (verticalStripUpperTailPolynomialNormalizerKernel a b N z).re ≤
        B * (1 + ‖z‖) ^ m) :
    ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  let X : ℝ :=
    C * (verticalStripUpperTailPolynomialNormalizerKernel a b N z).re
  have hfactor_norm :
      ‖verticalStripUpperTailPolynomialBoundedFactor f a b A C N z‖ =
        ‖A⁻¹‖ * (‖f z‖ * Real.exp (-X)) :=
    verticalStripUpperTailPolynomialBoundedFactor_norm_eq f a b A C N z
  have hAinv_nonneg : 0 ≤ A⁻¹ :=
    inv_nonneg.mpr (le_of_lt hA)
  have hAinv_norm : ‖A⁻¹‖ = A⁻¹ :=
    Real.norm_of_nonneg hAinv_nonneg
  have hunit_real :
      A⁻¹ * Real.exp (-X) * ‖f z‖ ≤ 1 := by
    have hrewrite :
        A⁻¹ * Real.exp (-X) * ‖f z‖ =
          ‖A⁻¹‖ * (‖f z‖ * Real.exp (-X)) := by
      calc
        A⁻¹ * Real.exp (-X) * ‖f z‖ =
            A⁻¹ * (Real.exp (-X) * ‖f z‖) :=
          mul_assoc A⁻¹ (Real.exp (-X)) ‖f z‖
        _ = A⁻¹ * (‖f z‖ * Real.exp (-X)) :=
          congrArg (fun y : ℝ => A⁻¹ * y)
            (mul_comm (Real.exp (-X)) ‖f z‖)
        _ = ‖A⁻¹‖ * (‖f z‖ * Real.exp (-X)) :=
          congrArg (fun y : ℝ => y * (‖f z‖ * Real.exp (-X)))
            hAinv_norm.symm
    Eq.subst
      (motive := fun T : ℝ => T ≤ 1)
      hrewrite.symm
      (Eq.subst
        (motive := fun T : ℝ => T ≤ 1)
        hfactor_norm
        hunit)
  have hraw :
      ‖f z‖ ≤ A * Real.exp X :=
    real_bound_of_scaled_exp_neg_unit hA hunit_real
  have hexp_le :
      Real.exp X ≤ Real.exp (B * (1 + ‖z‖) ^ m) :=
    Real.exp_le_exp.mpr hupper
  have hA_nonneg : 0 ≤ A :=
    le_of_lt hA
  exact
    le_trans hraw
      (mul_le_mul_of_nonneg_left hexp_le hA_nonneg)

/-- A unit bound for the degree-dependent polynomial bounded factor undamps to
the finite envelope once the real part of the polynomial kernel is bounded
above by that envelope exponent. -/
theorem verticalStripUpperTailDegreePolynomialBoundedFactor_undamps_to_finiteEnvelope
    (f : ℂ → ℂ)
    (a b A B C : ℝ)
    (m N : ℕ)
    (z : ℂ)
    (hA : 0 < A)
    (hunit :
      ‖verticalStripUpperTailDegreePolynomialBoundedFactor f a b A C N z‖ ≤ 1)
    (hupper :
      C * (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤
        B * (1 + ‖z‖) ^ m) :
    ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  let X : ℝ :=
    C * (verticalStripUpperTailDegreePolynomialKernel a b N z).re
  have hfactor_norm :
      ‖verticalStripUpperTailDegreePolynomialBoundedFactor f a b A C N z‖ =
        ‖A⁻¹‖ * (‖f z‖ * Real.exp (-X)) :=
    verticalStripUpperTailDegreePolynomialBoundedFactor_norm_eq f a b A C N z
  have hAinv_nonneg : 0 ≤ A⁻¹ :=
    inv_nonneg.mpr (le_of_lt hA)
  have hAinv_norm : ‖A⁻¹‖ = A⁻¹ :=
    Real.norm_of_nonneg hAinv_nonneg
  have hunit_real :
      A⁻¹ * Real.exp (-X) * ‖f z‖ ≤ 1 := by
    have hrewrite :
        A⁻¹ * Real.exp (-X) * ‖f z‖ =
          ‖A⁻¹‖ * (‖f z‖ * Real.exp (-X)) := by
      calc
        A⁻¹ * Real.exp (-X) * ‖f z‖ =
            A⁻¹ * (Real.exp (-X) * ‖f z‖) :=
          mul_assoc A⁻¹ (Real.exp (-X)) ‖f z‖
        _ = A⁻¹ * (‖f z‖ * Real.exp (-X)) :=
          congrArg (fun y : ℝ => A⁻¹ * y)
            (mul_comm (Real.exp (-X)) ‖f z‖)
        _ = ‖A⁻¹‖ * (‖f z‖ * Real.exp (-X)) :=
          congrArg (fun y : ℝ => y * (‖f z‖ * Real.exp (-X)))
            hAinv_norm.symm
    Eq.subst
      (motive := fun T : ℝ => T ≤ 1)
      hrewrite.symm
      (Eq.subst
        (motive := fun T : ℝ => T ≤ 1)
        hfactor_norm
        hunit)
  have hraw :
      ‖f z‖ ≤ A * Real.exp X :=
    real_bound_of_scaled_exp_neg_unit hA hunit_real
  have hexp_le :
      Real.exp X ≤ Real.exp (B * (1 + ‖z‖) ^ m) :=
    Real.exp_le_exp.mpr hupper
  have hA_nonneg : 0 ≤ A :=
    le_of_lt hA
  exact
    le_trans hraw
      (mul_le_mul_of_nonneg_left hexp_le hA_nonneg)

/-- A bounded normalized strip factor is uniformly bounded by one on the closed
strip once it has unit control on both vertical boundary lines. -/
theorem strip_boundedNormalizedFactor_uniform_bound
    (g : ℂ → ℂ)
    (a b : ℝ)
    (hg_hol : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b))
    (hg_finite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          g =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hg_left :
      ∀ z : ℂ, z.re = a → ‖g z‖ ≤ 1)
    (hg_right :
      ∀ z : ℂ, z.re = b → ‖g z‖ ≤ 1) :
    ∀ z : ℂ,
      a ≤ z.re →
      z.re ≤ b →
      ‖g z‖ ≤ 1 := by
  exact
    strip_uniform_bound_of_holomorphic_boundary_bound_and_mathlib_growth
      g a b 1 hg_hol hg_finite hg_left hg_right

/-- Undoing the bounded normalized upper-tail PL problem gives a finite-order
envelope for the original function on the upper tail. -/
theorem strip_finite_order_growth_upperTail_from_boundedNormalizedProblem_ownerGap
    (f g : ℂ → ℂ)
    (a b A₀ B₀ : ℝ)
    (m₀ : ℕ)
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hbound :
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖f z‖ ≤
          A₀ * Real.exp (B₀ * (1 + ‖z‖) ^ m₀) * ‖g z‖)
    (hg :
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖g z‖ ≤ 1) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    ⟨A₀, B₀, m₀, hA₀, hB₀,
      fun z hza hzb hzim =>
        have hraw :
            ‖f z‖ ≤
              A₀ * Real.exp (B₀ * (1 + ‖z‖) ^ m₀) * ‖g z‖ :=
          hbound z hza hzb hzim
        have hg_le_one : ‖g z‖ ≤ 1 :=
          hg z hza hzb
        le_trans hraw
          (finiteOrderEnvelope_mul_norm_le_self_of_norm_le_one
            A₀ B₀ m₀ z hA₀ g hg_le_one)⟩

/-- The bounded normalized upper-tail package gives the original fixed envelope
pointwise on the upper tail. -/
theorem strip_upperTail_fixedEnvelope_bound_of_boundedNormalizedProblem_package
    (f : ℂ → ℂ)
    (a b A₀ B₀ : ℝ)
    (m₀ : ℕ)
    (hA₀ : 0 < A₀)
    (hnormalized :
      ∃ g : ℂ → ℂ,
        DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b) ∧
        (∃ c : ℝ,
          c < Real.pi / (b - a) ∧
          ∃ D : ℝ,
            g =O[
                Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                  𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
              fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) ∧
        (∀ z : ℂ, z.re = a → ‖g z‖ ≤ 1) ∧
        (∀ z : ℂ, z.re = b → ‖g z‖ ≤ 1) ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          1 ≤ z.im →
          ‖f z‖ ≤
            A₀ * Real.exp (B₀ * (1 + ‖z‖) ^ m₀) * ‖g z‖) :
    ∀ z : ℂ,
      a ≤ z.re →
      z.re ≤ b →
      1 ≤ z.im →
      ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z‖) ^ m₀) := by
  match hnormalized with
  | ⟨g, hg_hol, hg_finite, hg_left, hg_right, hundo⟩ =>
      have hg_bound :
          ∀ z : ℂ,
            a ≤ z.re →
            z.re ≤ b →
            ‖g z‖ ≤ 1 :=
        strip_boundedNormalizedFactor_uniform_bound
          g a b hg_hol hg_finite hg_left hg_right
      exact
        fun z hza hzb hzim =>
          le_trans (hundo z hza hzb hzim)
            (finiteOrderEnvelope_mul_norm_le_self_of_norm_le_one
              A₀ B₀ m₀ z hA₀ g (hg_bound z hza hzb))

/-- Once the bounded normalized upper-tail package is available, the fixed
upper-tail envelope can be repackaged as a finite-order growth estimate. -/
theorem strip_finite_order_growth_upperTail_of_boundedNormalizedProblem_package
    (f : ℂ → ℂ)
    (a b A₀ B₀ : ℝ)
    (m₀ : ℕ)
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hnormalized :
      ∃ g : ℂ → ℂ,
        DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b) ∧
        (∃ c : ℝ,
          c < Real.pi / (b - a) ∧
          ∃ D : ℝ,
            g =O[
                Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                  𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
              fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) ∧
        (∀ z : ℂ, z.re = a → ‖g z‖ ≤ 1) ∧
        (∀ z : ℂ, z.re = b → ‖g z‖ ≤ 1) ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          1 ≤ z.im →
          ‖f z‖ ≤
            A₀ * Real.exp (B₀ * (1 + ‖z‖) ^ m₀) * ‖g z‖) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    ⟨A₀, B₀, m₀, hA₀, hB₀,
      strip_upperTail_fixedEnvelope_bound_of_boundedNormalizedProblem_package
        f a b A₀ B₀ m₀ hA₀ hnormalized⟩

/-- Core upper-tail finite-order Phragmen-Lindelöf step. -/
theorem strip_finite_order_growth_of_common_vertical_boundary_envelope_upperTail_normalized_PL_core_ownerGap
    (f : ℂ → ℂ)
    (a b A₀ B₀ : ℝ)
    (m₀ : ℕ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    strip_finite_order_growth_upperTail_finiteOrderPL_ownerGap
      f a b A₀ B₀ m₀ hab hhol hfinite hA₀ hB₀ hleft hright

/-- Upper-tail finite-order PL after fixing the common boundary envelope.

This public wrapper delegates to the finite-order upper half-strip core. -/
theorem strip_finite_order_growth_of_common_vertical_boundary_envelope_upperTail_from_normalized_PL_ownerGap
    (f : ℂ → ℂ)
    (a b A₀ B₀ : ℝ)
    (m₀ : ℕ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    strip_finite_order_growth_of_common_vertical_boundary_envelope_upperTail_normalized_PL_core_ownerGap
      f a b A₀ B₀ m₀ hab hhol hfinite hA₀ hB₀ hleft hright

/-- Upper vertical-tail component of the classical finite-order
Phragmen-Lindelöf theorem on a strip.

This is the genuine analytic half-strip step missing beyond mathlib's bounded
boundary theorem: polynomial finite-order control on both vertical sides and
subcritical interior growth propagate to the upper tail of the closed strip. -/
theorem strip_finite_order_growth_of_common_vertical_boundary_envelope_upperTail_classical_ownerGap
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hvertical_boundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))) :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          1 ≤ z.im →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  have hupper_boundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ z.im →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ z.im →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :=
    strip_upperTail_vertical_boundary_package_complex_height_bound
      f a b hvertical_boundary
  match hvertical_boundary, hupper_boundary with
  | ⟨A₀, B₀, m₀, hA₀, hB₀, hleft, hright⟩,
    ⟨_, _, _, _, _, _, _⟩ =>
      exact
        strip_finite_order_growth_of_common_vertical_boundary_envelope_upperTail_from_normalized_PL_ownerGap
          f a b A₀ B₀ m₀ hab hhol hfinite hA₀ hB₀ hleft hright

/-- Conjugation preserves membership in the open vertical strip. -/
theorem verticalStrip_reflection_openStrip_star_mem
    (a b : ℝ)
    (z : ℂ)
    (hz : z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    star z ∈ Complex.re ⁻¹' Set.Ioo a b := by
  match hz with
  | ⟨hleft, hright⟩ =>
      exact
        ⟨Eq.subst
            (motive := fun x : ℝ => a < x)
            (Complex.conj_re z).symm
            hleft,
          Eq.subst
            (motive := fun x : ℝ => x < b)
            (Complex.conj_re z).symm
            hright⟩

/-- The open vertical strip is open. -/
theorem verticalStrip_openStrip_isOpen
    (a b : ℝ) :
    IsOpen (Complex.re ⁻¹' Set.Ioo a b) := by
  exact isOpen_Ioo.preimage Complex.continuous_re

/-- Interior differentiability supplied by the `DiffContOnCl` strip package at
the reflected base point. -/
theorem verticalStrip_reflection_differentiableAt_reflectedBase_of_diffContOnCl
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (z : ℂ)
    (hz : star z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    DifferentiableAt ℂ f (star z) := by
  exact
    hhol.differentiableAt
      (verticalStrip_openStrip_isOpen a b)
      hz

/-- Pure local Schwarz sandwich for one complex-differentiable germ.

This is the remaining local power-series construction: a complex derivative at
`star z` is represented by multiplication by one coefficient, and conjugating
the source and target turns that coefficient into its conjugate, hence gives a
complex derivative for `w ↦ star (f (star w))` at `z`. -/
theorem differentiableWithinAt_conj_comp_conj_of_differentiableAt_reflectedBase_ownerConjugatedPowerSeries
    (f : ℂ → ℂ)
    (z : ℂ)
    (S : Set ℂ)
    (hf : DifferentiableAt ℂ f (star z)) :
    DifferentiableWithinAt ℂ
      (fun w : ℂ => star (f (star w)))
      S
      z := by
  have hHD :
      HasDerivAt (fun w : ℂ => star (f (star w))) (star (deriv f (star z))) z := by
    have hf' : Filter.Tendsto (slope f (star z)) (𝓝[≠] (star z)) (𝓝 (deriv f (star z))) :=
      hasDerivAt_iff_tendsto_slope.mp hf.hasDerivAt
    have hmaps : ∀ᶠ w : ℂ in 𝓝[≠] z, star w ≠ star z := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact fun heq => hw (star_injective heq)
    have hstarmap : Filter.Tendsto (fun w : ℂ => star w) (𝓝[≠] z) (𝓝[≠] (star z)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨(continuous_star.tendsto z).mono_left nhdsWithin_le_nhds, hmaps⟩
    have hcomp :
        Filter.Tendsto (fun w : ℂ => star (slope f (star z) (star w))) (𝓝[≠] z)
          (𝓝 (star (deriv f (star z)))) :=
      (continuous_star.tendsto (deriv f (star z))).comp (hf'.comp hstarmap)
    have hslope_eq :
        slope (fun w : ℂ => star (f (star w))) z
          = fun w : ℂ => star (slope f (star z) (star w)) := by
      funext w
      have hL : slope (fun w : ℂ => star (f (star w))) z w
          = (star (f (star w)) - star (f (star z))) / (w - z) := slope_def_field _ z w
      have hstar_den : star (star w - star z) = w - z :=
        (star_sub (star w) (star z)).trans
          (congrArg₂ (· - ·) (star_star w) (star_star z))
      have hstar_div :
          star ((f (star w) - f (star z)) / (star w - star z))
            = star (f (star w) - f (star z)) / star (star w - star z) :=
        calc star ((f (star w) - f (star z)) / (star w - star z))
            = star ((f (star w) - f (star z)) * (star w - star z)⁻¹) :=
              congrArg star (div_eq_mul_inv (f (star w) - f (star z)) (star w - star z))
          _ = star (f (star w) - f (star z)) * star ((star w - star z)⁻¹) :=
              star_mul' (f (star w) - f (star z)) (star w - star z)⁻¹
          _ = star (f (star w) - f (star z)) * (star (star w - star z))⁻¹ :=
              congrArg (fun t : ℂ => star (f (star w) - f (star z)) * t)
                (star_inv₀ (star w - star z))
          _ = star (f (star w) - f (star z)) / star (star w - star z) :=
              (div_eq_mul_inv (star (f (star w) - f (star z))) (star (star w - star z))).symm
      have hR : star (slope f (star z) (star w))
          = (star (f (star w)) - star (f (star z))) / (w - z) :=
        calc star (slope f (star z) (star w))
            = star ((f (star w) - f (star z)) / (star w - star z)) :=
              congrArg star (slope_def_field f (star z) (star w))
          _ = star (f (star w) - f (star z)) / star (star w - star z) := hstar_div
          _ = (star (f (star w)) - star (f (star z))) / (w - z) :=
              congrArg₂ (· / ·) (star_sub (f (star w)) (f (star z))) hstar_den
      exact hL.trans hR.symm
    exact hasDerivAt_iff_tendsto_slope.mpr (hslope_eq.symm ▸ hcomp)
  exact hHD.differentiableAt.differentiableWithinAt

/-- Local Schwarz reflection in the vertical strip, based at the conjugate
point, reduced to the conjugated local power-series model. -/
theorem verticalStrip_reflection_differentiableWithinAt_conj_comp_conj_reflectedBase_ownerConjugatedPowerSeries
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (z : ℂ)
    (hz : star z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    DifferentiableWithinAt ℂ
      (fun w : ℂ => star (f (star w)))
      (Complex.re ⁻¹' Set.Ioo a b)
      z := by
  exact
    differentiableWithinAt_conj_comp_conj_of_differentiableAt_reflectedBase_ownerConjugatedPowerSeries
      f z (Complex.re ⁻¹' Set.Ioo a b)
      (verticalStrip_reflection_differentiableAt_reflectedBase_of_diffContOnCl
        f a b hhol z hz)

/-- Local Schwarz reflection in the vertical strip, based at the conjugate
point. -/
theorem verticalStrip_reflection_differentiableWithinAt_conj_comp_conj_reflectedBase_ownerSchwarz
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (z : ℂ)
    (hz : star z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    DifferentiableWithinAt ℂ
      (fun w : ℂ => star (f (star w)))
      (Complex.re ⁻¹' Set.Ioo a b)
      z := by
  exact
    verticalStrip_reflection_differentiableWithinAt_conj_comp_conj_reflectedBase_ownerConjugatedPowerSeries
      f a b hhol z hz

-- Pointwise Schwarz-reflection differentiability transport on the open
-- vertical strip.  This is the local analytic core behind reflection of the
-- `DiffContOnCl` package.
/-- Local Schwarz sandwich for the reflected strip function at one point of the
open strip.

This is the genuinely anti-linear part of the reflection argument: it is not an
ordinary complex chain-rule consequence, because conjugation is not
complex-differentiable. -/
theorem verticalStrip_reflection_differentiableWithinAt_conj_comp_conj_localModel_ownerSchwarz
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (z : ℂ)
    (hz : z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    DifferentiableWithinAt ℂ
      (fun w : ℂ => star (f (star w)))
      (Complex.re ⁻¹' Set.Ioo a b)
      z := by
  exact
    verticalStrip_reflection_differentiableWithinAt_conj_comp_conj_reflectedBase_ownerSchwarz
      f a b hhol z
      (verticalStrip_reflection_openStrip_star_mem a b z hz)

/-- Local Schwarz sandwich for the reflected strip function at one point of the
open strip, reduced to the local conjugation model. -/
theorem verticalStrip_reflection_differentiableWithinAt_conj_comp_conj_local_ownerSchwarzSandwich
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (z : ℂ)
    (hz : z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    DifferentiableWithinAt ℂ
      (fun w : ℂ => star (f (star w)))
      (Complex.re ⁻¹' Set.Ioo a b)
      z := by
  exact
    verticalStrip_reflection_differentiableWithinAt_conj_comp_conj_localModel_ownerSchwarz
      f a b hhol z hz

/-- Pointwise Schwarz-reflection differentiability transport on the open
vertical strip.  This is the local analytic core behind reflection of the
`DiffContOnCl` package. -/
theorem verticalStrip_reflection_differentiableWithinAt_conj_comp_conj_pointwise_ownerSchwarzSandwich
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (z : ℂ)
    (hz : z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    DifferentiableWithinAt ℂ
      (fun w : ℂ => star (f (star w)))
      (Complex.re ⁻¹' Set.Ioo a b)
      z := by
  exact
    verticalStrip_reflection_differentiableWithinAt_conj_comp_conj_local_ownerSchwarzSandwich
      f a b hhol z hz

/-- Pointwise Schwarz-reflection differentiability transport on the open
vertical strip, packaged as a section over the strip. -/
theorem verticalStrip_reflection_differentiableWithinAt_conj_comp_conj_ownerSchwarzSandwich
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∀ z : ℂ,
      z ∈ Complex.re ⁻¹' Set.Ioo a b →
      DifferentiableWithinAt ℂ
        (fun w : ℂ => star (f (star w)))
        (Complex.re ⁻¹' Set.Ioo a b)
        z := by
  exact
    fun z hz =>
      verticalStrip_reflection_differentiableWithinAt_conj_comp_conj_pointwise_ownerSchwarzSandwich
        f a b hhol z hz

/-- Pointwise Schwarz-reflection differentiability transport on the open
vertical strip.  This is the local analytic core behind reflection of the
`DiffContOnCl` package. -/
theorem verticalStrip_reflection_differentiableAt_conj_comp_conj_ownerSchwarz
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∀ z : ℂ,
      z ∈ Complex.re ⁻¹' Set.Ioo a b →
      DifferentiableWithinAt ℂ
        (fun w : ℂ => star (f (star w)))
        (Complex.re ⁻¹' Set.Ioo a b)
        z := by
  exact
    verticalStrip_reflection_differentiableWithinAt_conj_comp_conj_ownerSchwarzSandwich
      f a b hhol

/-- Schwarz-reflection transport for the vertical-strip `DiffContOnCl` package.

The reflected function is `z ↦ conj (f (conj z))`.  This is the canonical
holomorphic reflection lemma needed by the lower-tail Phragmen-Lindelöf
reduction: conjugation preserves the real part and the two anti-holomorphic
conjugations cancel in the complex derivative. -/
theorem verticalStrip_reflection_differentiableOn_conj_comp_conj_ownerSchwarz
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    DifferentiableOn ℂ
      (fun z : ℂ => star (f (star z)))
      (Complex.re ⁻¹' Set.Ioo a b) := by
  exact
    verticalStrip_reflection_differentiableAt_conj_comp_conj_ownerSchwarz
      f a b hhol

/-- Conjugation preserves membership in the closed vertical strip. -/
theorem verticalStrip_reflection_closure_star_mem_ownerSchwarz
    (a b : ℝ)
    (z : ℂ)
    (hz : z ∈ closure (Complex.re ⁻¹' Set.Ioo a b)) :
    star z ∈ closure (Complex.re ⁻¹' Set.Ioo a b) := by
  exact
    map_mem_closure continuous_star hz
      (fun w hw =>
        verticalStrip_reflection_openStrip_star_mem a b w hw)

/-- Closure-filter Schwarz transport after the conjugation map has been
isolated. -/
theorem verticalStrip_reflection_continuousWithinAt_closure_conj_comp_conj_starMap_ownerSchwarz
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (z : ℂ)
    (hz : star z ∈ closure (Complex.re ⁻¹' Set.Ioo a b)) :
    ContinuousWithinAt
      (fun w : ℂ => star (f (star w)))
      (closure (Complex.re ⁻¹' Set.Ioo a b))
      z := by
  let S : Set ℂ := closure (Complex.re ⁻¹' Set.Ioo a b)
  have hstar_within :
      ContinuousWithinAt (fun w : ℂ => star w) S z :=
    continuousWithinAt_star
  have hf_within :
      ContinuousWithinAt f S (star z) :=
    hhol.continuousOn.continuousWithinAt hz
  have hstar_maps :
      Set.MapsTo (fun w : ℂ => star w) S S :=
    fun w hw =>
      verticalStrip_reflection_closure_star_mem_ownerSchwarz a b w hw
  have hcomp :
      ContinuousWithinAt
        (fun w : ℂ => f (star w))
        S
        z :=
    hf_within.comp hstar_within hstar_maps
  exact hcomp.star

/-- Closure-filter transport for Schwarz reflection on the closed vertical
strip.

Conjugation preserves the closed vertical strip and the neighborhood-within
filter at each reflected point; this is the exact topological transport needed
before applying the closed-strip continuity supplied by `DiffContOnCl`. -/
theorem verticalStrip_reflection_continuousWithinAt_closure_conj_comp_conj_comap_ownerSchwarz
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (z : ℂ)
    (hz : z ∈ closure (Complex.re ⁻¹' Set.Ioo a b)) :
    ContinuousWithinAt
      (fun w : ℂ => star (f (star w)))
      (closure (Complex.re ⁻¹' Set.Ioo a b))
      z := by
  exact
    verticalStrip_reflection_continuousWithinAt_closure_conj_comp_conj_starMap_ownerSchwarz
      f a b hhol z
      (verticalStrip_reflection_closure_star_mem_ownerSchwarz a b z hz)

/-- Closure-filter transport for Schwarz reflection on the closed vertical
strip, reduced to conjugation-comap of the closed-strip filter. -/
theorem verticalStrip_reflection_continuousWithinAt_closure_conj_comp_conj_filter_ownerSchwarzTransport
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (z : ℂ)
    (hz : z ∈ closure (Complex.re ⁻¹' Set.Ioo a b)) :
    ContinuousWithinAt
      (fun w : ℂ => star (f (star w)))
      (closure (Complex.re ⁻¹' Set.Ioo a b))
      z := by
  exact
    verticalStrip_reflection_continuousWithinAt_closure_conj_comp_conj_comap_ownerSchwarz
      f a b hhol z hz

/-- Pointwise boundary-continuity transport for Schwarz reflection on the
closed vertical strip. -/
theorem verticalStrip_reflection_continuousWithinAt_closure_conj_comp_conj_pointwise_ownerSchwarzTransport
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (z : ℂ)
    (hz : z ∈ closure (Complex.re ⁻¹' Set.Ioo a b)) :
    ContinuousWithinAt
      (fun w : ℂ => star (f (star w)))
      (closure (Complex.re ⁻¹' Set.Ioo a b))
      z := by
  exact
    verticalStrip_reflection_continuousWithinAt_closure_conj_comp_conj_filter_ownerSchwarzTransport
      f a b hhol z hz

/-- Pointwise boundary-continuity transport for Schwarz reflection on the
closed vertical strip, packaged as a section over the closed strip. -/
theorem verticalStrip_reflection_continuousWithinAt_closure_conj_comp_conj_ownerSchwarzTransport
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∀ z : ℂ,
      z ∈ closure (Complex.re ⁻¹' Set.Ioo a b) →
      ContinuousWithinAt
        (fun w : ℂ => star (f (star w)))
        (closure (Complex.re ⁻¹' Set.Ioo a b))
        z := by
  exact
    fun z hz =>
      verticalStrip_reflection_continuousWithinAt_closure_conj_comp_conj_pointwise_ownerSchwarzTransport
        f a b hhol z hz

/-- Pointwise boundary-continuity transport for Schwarz reflection on the
closed vertical strip. -/
theorem verticalStrip_reflection_continuousAt_closure_conj_comp_conj_ownerSchwarz
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∀ z : ℂ,
      z ∈ closure (Complex.re ⁻¹' Set.Ioo a b) →
      ContinuousWithinAt
        (fun w : ℂ => star (f (star w)))
        (closure (Complex.re ⁻¹' Set.Ioo a b))
        z := by
  exact
    verticalStrip_reflection_continuousWithinAt_closure_conj_comp_conj_ownerSchwarzTransport
      f a b hhol

/-- Boundary-continuity transport for Schwarz reflection on the closed vertical
strip attached to `Complex.re ⁻¹' Set.Ioo a b`. -/
theorem verticalStrip_reflection_continuousOn_closure_conj_comp_conj_ownerSchwarz
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ContinuousOn
      (fun z : ℂ => star (f (star z)))
      (closure (Complex.re ⁻¹' Set.Ioo a b)) := by
  exact
    verticalStrip_reflection_continuousAt_closure_conj_comp_conj_ownerSchwarz
      f a b hhol

/-- Schwarz-reflection transport for the vertical-strip `DiffContOnCl` package.

The reflected function is `z ↦ conj (f (conj z))`.  This is the canonical
holomorphic reflection lemma needed by the lower-tail Phragmen-Lindelöf
reduction: conjugation preserves the real part and the two anti-holomorphic
conjugations cancel in the complex derivative. -/
theorem verticalStrip_reflection_diffContOnCl_conj_comp_conj_ownerSchwarz
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    DiffContOnCl ℂ
      (fun z : ℂ => star (f (star z)))
      (Complex.re ⁻¹' Set.Ioo a b) := by
  exact
    ⟨verticalStrip_reflection_differentiableOn_conj_comp_conj_ownerSchwarz
        f a b hhol,
      verticalStrip_reflection_continuousOn_closure_conj_comp_conj_ownerSchwarz
        f a b hhol⟩

/-- Holomorphy-on-closed-strip transport for the reflected PL function
`z ↦ conj (f (conj z))`. -/
theorem strip_finite_order_growth_reflectedFunction_diffContOnCl_ownerGap
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    DiffContOnCl ℂ
      (fun z : ℂ => star (f (star z)))
      (Complex.re ⁻¹' Set.Ioo a b) := by
  exact
    verticalStrip_reflection_diffContOnCl_conj_comp_conj_ownerSchwarz
      f a b hhol

-- Subcritical finite-order Big-O transport under vertical-strip reflection.
-- The map `z ↦ conj z` preserves the vertical strip, preserves `|im z|`, and
-- preserves the height filter.  Taking the outer conjugate does not change the
-- norm, so the same constants witness the reflected finite-order estimate.
/-- Eventual-norm Big-O transport for the reflected strip function after
conjugating the height/strip filter.

This is the exact filter-comap step: the input Big-O estimate for `f` is used at
`star z`, while the right-hand side is unchanged because conjugation preserves
`|Im z|` and the outer star preserves norm. -/
theorem verticalStrip_reflection_finiteOrder_pointwiseNorm_ownerConjugationComapNorm
    (f : ℂ → ℂ)
    (c D : ℝ)
    (z : ℂ)
    (hbound :
      ‖f (star z)‖ ≤ Real.exp (D * Real.exp (c * |(star z).im|))) :
    ‖star (f (star z))‖ ≤ Real.exp (D * Real.exp (c * |z.im|)) := by
  have hnorm_star : ‖star (f (star z))‖ = ‖f (star z)‖ :=
    norm_star (f (star z))
  have him_abs : |(star z).im| = |z.im| := by
    calc
      |(star z).im| = |-z.im| := by
        exact congrArg (fun y : ℝ => |y|) (Complex.conj_im z)
      _ = |z.im| := by
        exact abs_neg z.im
  have hrhs :
      Real.exp (D * Real.exp (c * |(star z).im|)) =
        Real.exp (D * Real.exp (c * |z.im|)) :=
    congrArg
      (fun y : ℝ => Real.exp (D * Real.exp (c * y)))
      him_abs
  exact
    Eq.subst
      (motive := fun lhs : ℝ =>
        lhs ≤ Real.exp (D * Real.exp (c * |z.im|)))
      hnorm_star.symm
      (Eq.subst
        (motive := fun rhs : ℝ => ‖f (star z)‖ ≤ rhs)
        hrhs
        hbound)

/-- Conjugation preserves the height/open-strip filter used in finite-order
strip growth estimates. -/
theorem verticalStrip_reflection_heightStrip_star_tendsto_ownerConjugationComapNorm
    (a b : ℝ) :
    Filter.Tendsto
      (fun z : ℂ => star z)
      (Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
        𝓟 (Complex.re ⁻¹' Set.Ioo a b))
      (Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
        𝓟 (Complex.re ⁻¹' Set.Ioo a b)) := by
  let L : Filter ℂ :=
    Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo a b)
  have hheight_base :
      Filter.Tendsto (_root_.abs ∘ Complex.im) L Filter.atTop :=
    Filter.Tendsto.mono_left
      (tendsto_comap :
        Filter.Tendsto
          (_root_.abs ∘ Complex.im)
          (Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop)
          Filter.atTop)
      inf_le_left
  have hheight :
      Filter.Tendsto
        ((_root_.abs ∘ Complex.im) ∘ fun z : ℂ => star z)
        L
        Filter.atTop :=
    hheight_base.congr'
      (Filter.Eventually.of_forall
        fun z =>
        calc
          (_root_.abs ∘ Complex.im) z = |z.im| := rfl
          _ = |(star z).im| := by
            exact
              (Eq.trans
                (congrArg (fun y : ℝ => |y|) (Complex.conj_im z))
                (abs_neg z.im)).symm
          _ = ((_root_.abs ∘ Complex.im) ∘ fun w : ℂ => star w) z := rfl)
  have hstrip :
      Filter.Tendsto
        (fun z : ℂ => star z)
        L
        (𝓟 (Complex.re ⁻¹' Set.Ioo a b)) :=
    tendsto_principal.mpr
      ((Filter.eventually_inf_principal).2
        (Filter.Eventually.of_forall
          fun z hz =>
            verticalStrip_reflection_openStrip_star_mem a b z hz))
  exact
    tendsto_inf.2
      ⟨tendsto_comap_iff.2 hheight, hstrip⟩

/-- The finite-order comparison function is invariant under complex
conjugation. -/
theorem verticalStrip_reflection_finiteOrder_rhs_star_eq_ownerConjugationComapNorm
    (c D : ℝ)
    (z : ℂ) :
    Real.exp (D * Real.exp (c * |(star z).im|)) =
      Real.exp (D * Real.exp (c * |z.im|)) := by
  have him_abs : |(star z).im| = |z.im| := by
    calc
      |(star z).im| = |-z.im| := by
        exact congrArg (fun y : ℝ => |y|) (Complex.conj_im z)
      _ = |z.im| := by
        exact abs_neg z.im
  exact
    congrArg
      (fun y : ℝ => Real.exp (D * Real.exp (c * y)))
      him_abs

/-- Inner-comap finite-order transport for the height/strip filter under
complex conjugation. -/
theorem verticalStrip_reflection_finiteOrder_innerComap_ownerConjugationComapNorm
    (f : ℂ → ℂ)
    (a b c D : ℝ)
    (hf :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    (fun z : ℂ => f (star z)) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  let L : Filter ℂ :=
    Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo a b)
  let g : ℂ → ℝ :=
    fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))
  have hstar :
      Filter.Tendsto (fun z : ℂ => star z) L L :=
    verticalStrip_reflection_heightStrip_star_tendsto_ownerConjugationComapNorm
      a b
  have hcomp :
      (f ∘ fun z : ℂ => star z) =O[L] (g ∘ fun z : ℂ => star z) :=
    hf.comp_tendsto hstar
  have hright :
      (g ∘ fun z : ℂ => star z) =ᶠ[L] g :=
    Filter.Eventually.of_forall
      fun z =>
        verticalStrip_reflection_finiteOrder_rhs_star_eq_ownerConjugationComapNorm
          c D z
  exact
    hcomp.congr'
      (Filter.Eventually.of_forall fun _ => rfl)
      hright

/-- Comap transport for the height/strip filter under complex conjugation. -/
theorem verticalStrip_reflection_finiteOrder_filterComap_ownerConjugationComapNorm
    (f : ℂ → ℂ)
    (a b c D : ℝ)
    (hf :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    (fun z : ℂ => star (f (star z))) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  match (verticalStrip_reflection_finiteOrder_innerComap_ownerConjugationComapNorm
      f a b c D hf).bound with
  | ⟨C, hC⟩ =>
      exact
        Asymptotics.IsBigO.of_bound C
          (hC.mono
            fun z hz =>
              have hnorm_star :
                  ‖star (f (star z))‖ = ‖f (star z)‖ :=
                norm_star (f (star z))
              Eq.subst
                (motive := fun lhs : ℝ =>
                  lhs ≤
                    C * ‖Real.exp (D * Real.exp (c * |z.im|))‖)
                hnorm_star.symm
                hz)

theorem verticalStrip_reflection_finiteOrder_conj_comp_conj_eventualNorm_ownerConjugationComapNorm
    (f : ℂ → ℂ)
    (a b c D : ℝ)
    (hf :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    (fun z : ℂ => star (f (star z))) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    verticalStrip_reflection_finiteOrder_filterComap_ownerConjugationComapNorm
      f a b c D hf

/-- Eventual-norm Big-O transport for the reflected strip function after
conjugating the height/strip filter, reduced to the norm-preserving comap
calculation. -/
theorem verticalStrip_reflection_finiteOrder_conj_comp_conj_eventualNorm_ownerConjugationComapCore
    (f : ℂ → ℂ)
    (a b c D : ℝ)
    (hf :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    (fun z : ℂ => star (f (star z))) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    verticalStrip_reflection_finiteOrder_conj_comp_conj_eventualNorm_ownerConjugationComapNorm
      f a b c D hf

/-- Subcritical finite-order Big-O transport under vertical-strip reflection.

The map `z ↦ conj z` preserves the vertical strip, preserves `|im z|`, and
preserves the height filter.  Taking the outer conjugate does not change the
norm, so the same constants witness the reflected finite-order estimate. -/
theorem verticalStrip_reflection_finiteOrder_conj_comp_conj_eventualNorm_ownerConjugationComap
    (f : ℂ → ℂ)
    (a b c D : ℝ)
    (hf :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    (fun z : ℂ => star (f (star z))) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    verticalStrip_reflection_finiteOrder_conj_comp_conj_eventualNorm_ownerConjugationComapCore
      f a b c D hf

/-- Subcritical finite-order Big-O transport under vertical-strip reflection,
reduced to conjugation invariance of the height/strip filter. -/
theorem verticalStrip_reflection_finiteOrder_conj_comp_conj_eventualNorm_ownerHeightFilterInvariance
    (f : ℂ → ℂ)
    (a b c D : ℝ)
    (hf :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    (fun z : ℂ => star (f (star z))) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    verticalStrip_reflection_finiteOrder_conj_comp_conj_eventualNorm_ownerConjugationComap
      f a b c D hf

/-- Subcritical finite-order Big-O transport under vertical-strip reflection.

The map `z ↦ conj z` preserves the vertical strip, preserves `|im z|`, and
preserves the height filter.  Taking the outer conjugate does not change the
norm, so the same constants witness the reflected finite-order estimate. -/
theorem verticalStrip_reflection_finiteOrder_conj_comp_conj_eventualNorm_ownerFilterTransport
    (f : ℂ → ℂ)
    (a b c D : ℝ)
    (hf :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    (fun z : ℂ => star (f (star z))) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    verticalStrip_reflection_finiteOrder_conj_comp_conj_eventualNorm_ownerHeightFilterInvariance
      f a b c D hf

/-- Subcritical finite-order Big-O transport under vertical-strip reflection.

The map `z ↦ conj z` preserves the vertical strip, preserves `|im z|`, and
preserves the height filter.  Taking the outer conjugate does not change the
norm, so the same constants witness the reflected finite-order estimate. -/
theorem verticalStrip_reflection_finiteOrder_conj_comp_conj_witness_ownerFilterTransport
    (f : ℂ → ℂ)
    (a b c D : ℝ)
    (hf :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    (fun z : ℂ => star (f (star z))) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    verticalStrip_reflection_finiteOrder_conj_comp_conj_eventualNorm_ownerFilterTransport
      f a b c D hf

/-- Subcritical finite-order Big-O transport under vertical-strip reflection.

The map `z ↦ conj z` preserves the vertical strip, preserves `|im z|`, and
preserves the height filter.  Taking the outer conjugate does not change the
norm, so the same constants witness the reflected finite-order estimate. -/
theorem verticalStrip_reflection_finiteOrder_conj_comp_conj_ownerBigO
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    ∃ c : ℝ,
      c < Real.pi / (b - a) ∧
      ∃ D : ℝ,
        (fun z : ℂ => star (f (star z))) =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  match hfinite with
  | ⟨c, hc, D, hD⟩ =>
      exact
        ⟨c, hc, D,
          verticalStrip_reflection_finiteOrder_conj_comp_conj_witness_ownerFilterTransport
            f a b c D hD⟩

/-- Finite-order transport for the reflected PL function
`z ↦ conj (f (conj z))`. -/
theorem strip_finite_order_growth_reflectedFunction_finiteOrder_ownerGap
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    ∃ c : ℝ,
      c < Real.pi / (b - a) ∧
      ∃ D : ℝ,
        (fun z : ℂ => star (f (star z))) =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    verticalStrip_reflection_finiteOrder_conj_comp_conj_ownerBigO
      f a b hfinite

/-- Left-boundary envelope transport for the reflected PL function. -/
theorem strip_finite_order_growth_reflectedFunction_leftBoundary_ownerGap
    (f : ℂ → ℂ)
    (a A₀ B₀ : ℝ)
    (m₀ : ℕ)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀)) :
    ∀ z : ℂ,
      z.re = a →
      1 ≤ ‖z.im‖ →
      ‖star (f (star z))‖ ≤
        A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀) := by
  intro z hz hzim
  let w : ℂ := star z
  have hw_re : w.re = a :=
    Eq.trans (Complex.conj_re z) hz
  have hw_im_norm : ‖w.im‖ = ‖z.im‖ := by
    calc
      ‖w.im‖ = ‖-z.im‖ := by
        exact congrArg (fun y : ℝ => ‖y‖) (Complex.conj_im z)
      _ = ‖z.im‖ := by
        exact norm_neg z.im
  have hw_im : 1 ≤ ‖w.im‖ :=
    Eq.subst
      (motive := fun x : ℝ => 1 ≤ x)
      hw_im_norm.symm
      hzim
  have hbound :
      ‖f w‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖w.im‖) ^ m₀) :=
    hleft w hw_re hw_im
  have hnorm_star : ‖star (f w)‖ = ‖f w‖ :=
    norm_star (f w)
  have hrhs :
      A₀ * Real.exp (B₀ * (1 + ‖w.im‖) ^ m₀) =
        A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀) := by
    exact congrArg
      (fun y : ℝ => A₀ * Real.exp (B₀ * (1 + y) ^ m₀))
      hw_im_norm
  exact
    Eq.subst
      (motive := fun lhs : ℝ =>
        lhs ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀))
      hnorm_star.symm
      (Eq.subst
        (motive := fun rhs : ℝ => ‖f w‖ ≤ rhs)
        hrhs
        hbound)

/-- Right-boundary envelope transport for the reflected PL function. -/
theorem strip_finite_order_growth_reflectedFunction_rightBoundary_ownerGap
    (f : ℂ → ℂ)
    (b A₀ B₀ : ℝ)
    (m₀ : ℕ)
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀)) :
    ∀ z : ℂ,
      z.re = b →
      1 ≤ ‖z.im‖ →
      ‖star (f (star z))‖ ≤
        A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀) := by
  intro z hz hzim
  let w : ℂ := star z
  have hw_re : w.re = b :=
    Eq.trans (Complex.conj_re z) hz
  have hw_im_norm : ‖w.im‖ = ‖z.im‖ := by
    calc
      ‖w.im‖ = ‖-z.im‖ := by
        exact congrArg (fun y : ℝ => ‖y‖) (Complex.conj_im z)
      _ = ‖z.im‖ := by
        exact norm_neg z.im
  have hw_im : 1 ≤ ‖w.im‖ :=
    Eq.subst
      (motive := fun x : ℝ => 1 ≤ x)
      hw_im_norm.symm
      hzim
  have hbound :
      ‖f w‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖w.im‖) ^ m₀) :=
    hright w hw_re hw_im
  have hnorm_star : ‖star (f w)‖ = ‖f w‖ :=
    norm_star (f w)
  have hrhs :
      A₀ * Real.exp (B₀ * (1 + ‖w.im‖) ^ m₀) =
        A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀) := by
    exact congrArg
      (fun y : ℝ => A₀ * Real.exp (B₀ * (1 + y) ^ m₀))
      hw_im_norm
  exact
    Eq.subst
      (motive := fun lhs : ℝ =>
        lhs ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀))
      hnorm_star.symm
      (Eq.subst
        (motive := fun rhs : ℝ => ‖f w‖ ≤ rhs)
        hrhs
        hbound)

/-- Pull the upper-tail bound for the reflected PL function back to the lower
tail of the original function. -/
theorem strip_finite_order_growth_reflectedUpperTail_pullback_ownerGap
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hupper :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          1 ≤ z.im →
          ‖star (f (star z))‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        z.im ≤ -1 →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hupper with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      exact
        ⟨A, B, m, hA, hB,
          fun z hza hzb hzim =>
            let w : ℂ := star z
            have hw_re : w.re = z.re :=
              Complex.conj_re z
            have hw_lower : a ≤ w.re :=
              Eq.subst
                (motive := fun x : ℝ => a ≤ x)
                hw_re.symm
                hza
            have hw_upper : w.re ≤ b :=
              Eq.subst
                (motive := fun x : ℝ => x ≤ b)
                hw_re.symm
                hzb
            have hw_im : 1 ≤ w.im := by
              have hneg_one_le_neg : (1 : ℝ) ≤ -z.im :=
                calc
                  (1 : ℝ) = -(-1 : ℝ) := by
                    exact (neg_neg (1 : ℝ)).symm
                  _ ≤ -z.im :=
                    neg_le_neg hzim
              have hw_im_eq : w.im = -z.im :=
                Complex.conj_im z
              exact
                Eq.subst
                  (motive := fun x : ℝ => 1 ≤ x)
                  hw_im_eq.symm
                  hneg_one_le_neg
            have hw_norm : ‖w‖ = ‖z‖ :=
              norm_star z
            have hstar_w : star w = z :=
              star_star z
            have hupper_w :
                ‖star (f (star w))‖ ≤
                  A * Real.exp (B * (1 + ‖w‖) ^ m) :=
              hbound w hw_lower hw_upper hw_im
            have hlhs :
                ‖star (f (star w))‖ = ‖f z‖ := by
              have harg :
                  f (star w) = f z :=
                congrArg f hstar_w
              have hstar_arg :
                  star (f (star w)) = star (f z) :=
                congrArg star harg
              have hnorm₁ :
                  ‖star (f (star w))‖ = ‖star (f z)‖ :=
                congrArg (fun y : ℂ => ‖y‖) hstar_arg
              have hnorm₂ :
                  ‖star (f z)‖ = ‖f z‖ :=
                norm_star (f z)
              exact Eq.trans hnorm₁ hnorm₂
            have hrhs :
                A * Real.exp (B * (1 + ‖w‖) ^ m) =
                  A * Real.exp (B * (1 + ‖z‖) ^ m) := by
              exact congrArg
                (fun y : ℝ => A * Real.exp (B * (1 + y) ^ m))
                hw_norm
            Eq.subst
              (motive := fun lhs : ℝ =>
                lhs ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
              hlhs
              (Eq.subst
                (motive := fun rhs : ℝ => ‖star (f (star w))‖ ≤ rhs)
                hrhs
                hupper_w)⟩

/-- Reflection package reducing the lower normalized tail to the upper
normalized Phragmen-Lindelöf tail.

The intended reflected function is `z ↦ conj (f (conj z))`.  The remaining
content is exactly the reflection transport of holomorphy on the vertical
strip, the subcritical finite-order estimate, the shared vertical boundary
envelope, and the final conjugation/norm pullback from `-z.im ≥ 1` to
`z.im ≤ -1`. -/
theorem strip_finite_order_growth_of_common_vertical_boundary_envelope_lowerTail_reflection_to_upper_ownerGap
    (f : ℂ → ℂ)
    (a b A₀ B₀ : ℝ)
    (m₀ : ℕ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        z.im ≤ -1 →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  have hreflect_hol :
      DiffContOnCl ℂ
        (fun z : ℂ => star (f (star z)))
        (Complex.re ⁻¹' Set.Ioo a b) :=
    strip_finite_order_growth_reflectedFunction_diffContOnCl_ownerGap
      f a b hhol
  have hreflect_finite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          (fun z : ℂ => star (f (star z))) =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) :=
    strip_finite_order_growth_reflectedFunction_finiteOrder_ownerGap
      f a b hfinite
  have hreflect_left :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖star (f (star z))‖ ≤
          A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀) :=
    strip_finite_order_growth_reflectedFunction_leftBoundary_ownerGap
      f a A₀ B₀ m₀ hleft
  have hreflect_right :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖star (f (star z))‖ ≤
          A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀) :=
    strip_finite_order_growth_reflectedFunction_rightBoundary_ownerGap
      f b A₀ B₀ m₀ hright
  have hupper :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          1 ≤ z.im →
          ‖star (f (star z))‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    strip_finite_order_growth_of_common_vertical_boundary_envelope_upperTail_normalized_PL_core_ownerGap
      (fun z : ℂ => star (f (star z)))
      a b A₀ B₀ m₀ hab hreflect_hol hreflect_finite hA₀ hB₀
      hreflect_left hreflect_right
  exact
    strip_finite_order_growth_reflectedUpperTail_pullback_ownerGap
      f a b hupper

/-- Core lower-tail normalized Phragmen-Lindelöf step.

This is the reflected companion to
`strip_finite_order_growth_of_common_vertical_boundary_envelope_upperTail_normalized_PL_core_ownerGap`.
The proof should either apply the same normalized vertical-strip
Phragmen-Lindelöf argument on the lower half-strip directly, or transport the
upper-half-strip core across the antiholomorphic reflection after explicitly
proving the reflected holomorphy, finite-order, and boundary-envelope data. -/
theorem strip_finite_order_growth_of_common_vertical_boundary_envelope_lowerTail_normalized_PL_core_ownerGap
    (f : ℂ → ℂ)
    (a b A₀ B₀ : ℝ)
    (m₀ : ℕ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        z.im ≤ -1 →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    strip_finite_order_growth_of_common_vertical_boundary_envelope_lowerTail_reflection_to_upper_ownerGap
      f a b A₀ B₀ m₀ hab hhol hfinite hA₀ hB₀ hleft hright

/-- Lower-tail finite-order PL after fixing the common boundary envelope.

The public lower-tail theorem should only unpack the shared vertical boundary
envelope.  The analytic work belongs to the normalized lower-tail core. -/
theorem strip_finite_order_growth_of_common_vertical_boundary_envelope_lowerTail_from_normalized_PL_ownerGap
    (f : ℂ → ℂ)
    (a b A₀ B₀ : ℝ)
    (m₀ : ℕ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hA₀ : 0 < A₀)
    (hB₀ : 0 < B₀)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A₀ * Real.exp (B₀ * (1 + ‖z.im‖) ^ m₀)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        z.im ≤ -1 →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    strip_finite_order_growth_of_common_vertical_boundary_envelope_lowerTail_normalized_PL_core_ownerGap
      f a b A₀ B₀ m₀ hab hhol hfinite hA₀ hB₀ hleft hright

/-- Lower vertical-tail component of the classical finite-order
Phragmen-Lindelöf theorem on a strip.

This is the reflected lower half-strip companion to
`strip_finite_order_growth_of_common_vertical_boundary_envelope_upperTail_classical_ownerGap`. -/
theorem strip_finite_order_growth_of_common_vertical_boundary_envelope_lowerTail_classical_ownerGap
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hvertical_boundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        z.im ≤ -1 →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hvertical_boundary with
  | ⟨A₀, B₀, m₀, hA₀, hB₀, hleft, hright⟩ =>
      exact
        strip_finite_order_growth_of_common_vertical_boundary_envelope_lowerTail_from_normalized_PL_ownerGap
          f a b A₀ B₀ m₀ hab hhol hfinite hA₀ hB₀ hleft hright

/-- A point with `1 ≤ ‖im z‖` lies in one of the two vertical tails. -/
theorem vertical_abs_ge_one_tail_cases
    (z : ℂ)
    (hz : 1 ≤ ‖z.im‖) :
    1 ≤ z.im ∨ z.im ≤ -1 := by
  have hnorm_abs : ‖z.im‖ = |z.im| :=
    Real.norm_eq_abs z.im
  have habs : 1 ≤ |z.im| :=
    Eq.subst
      (motive := fun x : ℝ => 1 ≤ x)
      hnorm_abs
      hz
  have hcases : z.im < 0 ∨ 0 ≤ z.im := lt_or_ge z.im 0
  match hcases with
  | Or.inl hneg =>
      have habs_eq : |z.im| = -z.im :=
        abs_of_neg hneg
      have hle_neg : 1 ≤ -z.im :=
        Eq.subst
          (motive := fun x : ℝ => 1 ≤ x)
          habs_eq
          habs
      have hz_le : z.im ≤ -1 := by
        calc
          z.im = -(-z.im) := by
            exact (neg_neg z.im).symm
          _ ≤ -1 :=
            neg_le_neg hle_neg
      exact Or.inr hz_le
  | Or.inr hnonneg =>
      have habs_eq : |z.im| = z.im :=
        abs_of_nonneg hnonneg
      have hle_pos : 1 ≤ z.im :=
        Eq.subst
          (motive := fun x : ℝ => 1 ≤ x)
          habs_eq
          habs
      exact Or.inl hle_pos

/-- Assemble the two vertical-tail finite-order PL estimates into the closed
strip estimate stated with `‖im z‖`.

This lemma is purely bookkeeping: the analytic content is exactly the upper
and lower half-strip Phragmen-Lindelöf components. -/
theorem strip_finite_order_growth_of_common_vertical_boundary_envelope_of_tail_components
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hupper :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          1 ≤ z.im →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hlower :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          z.im ≤ -1 →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hupper, hlower with
  | ⟨Au, Bu, mu, hAu, hBu, hupper_bound⟩,
    ⟨Al, Bl, ml, hAl, hBl, hlower_bound⟩ =>
      let A : ℝ := Au + Al
      let B : ℝ := Bu + Bl
      let m : ℕ := mu + ml
      have hA_pos : 0 < A := add_pos hAu hAl
      have hB_pos : 0 < B := add_pos hBu hBl
      have hupper_common :
          ∀ z : ℂ,
            a ≤ z.re →
            z.re ≤ b →
            1 ≤ z.im →
            ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
        fun z hza hzb hzim =>
          le_trans (hupper_bound z hza hzb hzim)
            (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
              (le_of_lt hAu)
              (le_add_of_nonneg_right (le_of_lt hAl))
              (le_add_of_nonneg_right (le_of_lt hBl))
              (le_of_lt hBu)
              (Nat.le_add_right mu ml))
      have hlower_common :
          ∀ z : ℂ,
            a ≤ z.re →
            z.re ≤ b →
            z.im ≤ -1 →
            ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
        fun z hza hzb hzim =>
          have hdegree : ml ≤ mu + ml :=
            Eq.subst
              (motive := fun d : ℕ => ml ≤ d)
              (Nat.add_comm ml mu)
              (Nat.le_add_right ml mu)
          le_trans (hlower_bound z hza hzb hzim)
            (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
              (le_of_lt hAl)
              (le_add_of_nonneg_left (le_of_lt hAu))
              (le_add_of_nonneg_left (le_of_lt hBu))
              (le_of_lt hBl)
              hdegree)
      exact
        ⟨A, B, m, hA_pos, hB_pos,
          fun z hza hzb hz_im =>
            match vertical_abs_ge_one_tail_cases z hz_im with
            | Or.inl hupper_tail =>
                hupper_common z hza hzb hupper_tail
            | Or.inr hlower_tail =>
                hlower_common z hza hzb hlower_tail⟩

/-- Classical finite-order Phragmen-Lindelöf theorem for a vertical strip.

This is the precise missing analytic theorem after the bounded-boundary theorem:
holomorphy on the strip, subcritical interior growth, and finite-order boundary
envelopes on the two vertical sides imply a finite-order envelope throughout the
closed strip.  It is not supplied by the current cosine endpoint damping,
because that kernel has modulus one on the boundary lines. -/
theorem strip_finite_order_growth_of_common_vertical_boundary_envelope_classical_ownerGap
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hvertical_boundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  have hupper :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          1 ≤ z.im →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    strip_finite_order_growth_of_common_vertical_boundary_envelope_upperTail_classical_ownerGap
      f a b hab hhol hfinite hvertical_boundary
  have hlower :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          z.im ≤ -1 →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    strip_finite_order_growth_of_common_vertical_boundary_envelope_lowerTail_classical_ownerGap
      f a b hab hhol hfinite hvertical_boundary
  exact
    strip_finite_order_growth_of_common_vertical_boundary_envelope_of_tail_components
      f a b hupper hlower

/-- Common vertical-height finite-order boundary envelopes propagate through the strip
by the classical finite-order Phragmen-Lindelöf theorem.

This wrapper keeps the already-proved normalization from complex-height boundary
envelopes to vertical-height envelopes separate from the still-missing classical
finite-order strip theorem. -/
theorem strip_finite_order_growth_of_common_vertical_boundary_envelope_by_classical_PL
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hvertical_boundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    strip_finite_order_growth_of_common_vertical_boundary_envelope_classical_ownerGap
      f a b hab hhol hfinite hvertical_boundary

/-- Vertical-strip Phragmen-Lindelöf growth theorem with genuine finite-order
boundary input.

The boundary hypotheses are ordinary finite-order envelopes on the two vertical
sides.  The remaining analytic input is the classical finite-order
Phragmen-Lindelöf strip theorem, not the false cosine-boundary damping step. -/
theorem strip_finite_order_growth_of_boundary_envelopes_by_damping
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  have hvertical_boundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :=
    strip_boundary_envelopes_common_vertical_height_bound
      f a b hab hleft hright
  exact
    strip_finite_order_growth_of_common_vertical_boundary_envelope_by_classical_PL
      f a b hab hhol hfinite hvertical_boundary

end
end LFunctions
end Boundary
