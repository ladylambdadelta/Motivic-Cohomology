import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveProtectedResidual

/-!
# Protected finite inactive reciprocal series

The full-support protected residuals are inserted into the square, cube, and
fourth-power reciprocal series.  Both finite inactive classes are injected
into zero-based natural series without adding a fictitious small-gap mode.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.finiteLeftProtected_inverseSquare_eq_zeroBasedTerm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    1 / (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2 =
      Real.zeroBasedShiftedInverseSquareTerm
        (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a)
        (2 * Real.pi)
        (Complex.logarithmicPhaseFiniteLeftProtectedIndex m) := by
  unfold Real.zeroBasedShiftedInverseSquareTerm
  exact congrArg (fun value : ℝ => 1 / value ^ 2)
    (Complex.logarithmicPhaseFiniteLeftProtectedResidual_add_step
      t ht a b ha hab m).symm

theorem Complex.finiteLeftProtected_inverseCube_eq_zeroBasedTerm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    1 / (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 3 =
      Real.zeroBasedShiftedInverseCubeTerm
        (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a)
        (2 * Real.pi)
        (Complex.logarithmicPhaseFiniteLeftProtectedIndex m) := by
  unfold Real.zeroBasedShiftedInverseCubeTerm
  exact congrArg (fun value : ℝ => 1 / value ^ 3)
    (Complex.logarithmicPhaseFiniteLeftProtectedResidual_add_step
      t ht a b ha hab m).symm

theorem Complex.finiteLeftProtected_inverseFourth_eq_zeroBasedTerm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    1 / (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 4 =
      Real.zeroBasedShiftedInverseFourthTerm
        (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a)
        (2 * Real.pi)
        (Complex.logarithmicPhaseFiniteLeftProtectedIndex m) := by
  unfold Real.zeroBasedShiftedInverseFourthTerm
  exact congrArg (fun value : ℝ => 1 / value ^ 4)
    (Complex.logarithmicPhaseFiniteLeftProtectedResidual_add_step
      t ht a b ha hab m).symm

theorem Complex.finiteRightProtected_inverseSquare_eq_zeroBasedTerm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    1 / (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 2 =
      Real.zeroBasedShiftedInverseSquareTerm
        (Complex.logarithmicPhaseFiniteRightProtectedResidual t b)
        (2 * Real.pi)
        (Complex.logarithmicPhaseFiniteRightProtectedIndex m) := by
  unfold Real.zeroBasedShiftedInverseSquareTerm
  exact congrArg (fun value : ℝ => 1 / value ^ 2)
    (Complex.logarithmicPhaseFiniteRightProtectedResidual_add_step
      t ht a b ha hab m).symm

theorem Complex.finiteRightProtected_inverseCube_eq_zeroBasedTerm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    1 / (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 3 =
      Real.zeroBasedShiftedInverseCubeTerm
        (Complex.logarithmicPhaseFiniteRightProtectedResidual t b)
        (2 * Real.pi)
        (Complex.logarithmicPhaseFiniteRightProtectedIndex m) := by
  unfold Real.zeroBasedShiftedInverseCubeTerm
  exact congrArg (fun value : ℝ => 1 / value ^ 3)
    (Complex.logarithmicPhaseFiniteRightProtectedResidual_add_step
      t ht a b ha hab m).symm

theorem Complex.finiteRightProtected_inverseFourth_eq_zeroBasedTerm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    1 / (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 4 =
      Real.zeroBasedShiftedInverseFourthTerm
        (Complex.logarithmicPhaseFiniteRightProtectedResidual t b)
        (2 * Real.pi)
        (Complex.logarithmicPhaseFiniteRightProtectedIndex m) := by
  unfold Real.zeroBasedShiftedInverseFourthTerm
  exact congrArg (fun value : ℝ => 1 / value ^ 4)
    (Complex.logarithmicPhaseFiniteRightProtectedResidual_add_step
      t ht a b ha hab m).symm

theorem Finset.sum_protected_inverse_power_le_tsum
    {α : Type*} [DecidableEq α]
    (modes : Finset α) (f : α → ℝ) (g : ℕ → ℝ)
    (index : {x : α // x ∈ modes} → ℕ)
    (hinjective : Function.Injective index)
    (hpoint : ∀ x : {x : α // x ∈ modes}, f x ≤ g (index x))
    (hseriesNonneg : ∀ n : ℕ, 0 ≤ g n)
    (hsummable : Summable g) :
    (∑ x ∈ modes, f x) ≤ ∑' n : ℕ, g n := by
  exact Finset.sum_le_tsum_of_subtype_injection
    modes f g index hinjective hpoint hseriesNonneg hsummable

theorem Complex.sum_finiteLeftProtected_inverseSquare_le_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
      1 / (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) ≤
      Real.zeroBasedShiftedInverseSquareBudget
        (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a)
        (2 * Real.pi) := by
  let modes := Complex.logarithmicPhasePoissonLeftInactiveModes t a b
  let f : ℤ → ℝ := fun m => 1 /
    (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2
  let g := Real.zeroBasedShiftedInverseSquareTerm
    (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a) (2 * Real.pi)
  have hresidual := Complex.logarithmicPhaseFiniteLeftProtectedResidual_pos
    t ht a ha
  have hgNonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    unfold g
    unfold Real.zeroBasedShiftedInverseSquareTerm
    have hbase := add_nonneg hresidual.le
      (mul_nonneg Complex.two_mul_pi_pos.le (Nat.cast_nonneg n))
    exact div_nonneg zero_le_one (pow_nonneg hbase 2)
  have hsum := Finset.sum_protected_inverse_power_le_tsum modes f g
    Complex.logarithmicPhaseFiniteLeftProtectedIndex
    (Complex.logarithmicPhaseFiniteLeftProtectedIndex_injective
      t ht a b ha hab)
    (fun m => le_of_eq
      (Complex.finiteLeftProtected_inverseSquare_eq_zeroBasedTerm
        t ht a b ha hab m))
    hgNonneg
    (Real.summable_zeroBasedShiftedInverseSquareTerm
      _ _ hresidual Complex.two_mul_pi_pos)
  exact le_trans hsum
    (Real.tsum_zeroBasedShiftedInverseSquareTerm_le_budget
      _ _ hresidual Complex.two_mul_pi_pos)

theorem Complex.sum_finiteRightProtected_inverseSquare_le_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
      1 / (Complex.logarithmicPhaseRightInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 2) ≤
      Real.zeroBasedShiftedInverseSquareBudget
        (Complex.logarithmicPhaseFiniteRightProtectedResidual t b)
        (2 * Real.pi) := by
  let modes := Complex.logarithmicPhasePoissonRightInactiveModes t a b
  let f : ℤ → ℝ := fun m => 1 /
    (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 2
  let g := Real.zeroBasedShiftedInverseSquareTerm
    (Complex.logarithmicPhaseFiniteRightProtectedResidual t b) (2 * Real.pi)
  have hresidual := Complex.logarithmicPhaseFiniteRightProtectedResidual_pos
    t ht a b ha hab
  have hgNonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    unfold g
    unfold Real.zeroBasedShiftedInverseSquareTerm
    have hbase := add_nonneg hresidual.le
      (mul_nonneg Complex.two_mul_pi_pos.le (Nat.cast_nonneg n))
    exact div_nonneg zero_le_one (pow_nonneg hbase 2)
  have hsum := Finset.sum_protected_inverse_power_le_tsum modes f g
    Complex.logarithmicPhaseFiniteRightProtectedIndex
    (Complex.logarithmicPhaseFiniteRightProtectedIndex_injective
      t ht a b ha hab)
    (fun m => le_of_eq
      (Complex.finiteRightProtected_inverseSquare_eq_zeroBasedTerm
        t ht a b ha hab m))
    hgNonneg
    (Real.summable_zeroBasedShiftedInverseSquareTerm
      _ _ hresidual Complex.two_mul_pi_pos)
  exact le_trans hsum
    (Real.tsum_zeroBasedShiftedInverseSquareTerm_le_budget
      _ _ hresidual Complex.two_mul_pi_pos)

theorem Complex.sum_finiteLeftProtected_inverseCube_le_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
      1 / (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 3) ≤
      Real.zeroBasedShiftedInverseCubeBudget
        (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a)
        (2 * Real.pi) := by
  let modes := Complex.logarithmicPhasePoissonLeftInactiveModes t a b
  let f : ℤ → ℝ := fun m => 1 /
    (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 3
  let g := Real.zeroBasedShiftedInverseCubeTerm
    (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a) (2 * Real.pi)
  have hresidual := Complex.logarithmicPhaseFiniteLeftProtectedResidual_pos
    t ht a ha
  have hgNonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    unfold g
    unfold Real.zeroBasedShiftedInverseCubeTerm
    have hbase := add_nonneg hresidual.le
      (mul_nonneg Complex.two_mul_pi_pos.le (Nat.cast_nonneg n))
    exact div_nonneg zero_le_one (pow_nonneg hbase 3)
  have hsum := Finset.sum_protected_inverse_power_le_tsum modes f g
    Complex.logarithmicPhaseFiniteLeftProtectedIndex
    (Complex.logarithmicPhaseFiniteLeftProtectedIndex_injective
      t ht a b ha hab)
    (fun m => le_of_eq
      (Complex.finiteLeftProtected_inverseCube_eq_zeroBasedTerm
        t ht a b ha hab m))
    hgNonneg
    (Real.summable_zeroBasedShiftedInverseCubeTerm
      _ _ hresidual Complex.two_mul_pi_pos)
  exact le_trans hsum
    (Real.tsum_zeroBasedShiftedInverseCubeTerm_le_budget
      _ _ hresidual Complex.two_mul_pi_pos)

theorem Complex.sum_finiteLeftProtected_inverseFourth_le_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
      1 / (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 4) ≤
      Real.zeroBasedShiftedInverseFourthBudget
        (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a)
        (2 * Real.pi) := by
  let modes := Complex.logarithmicPhasePoissonLeftInactiveModes t a b
  let f : ℤ → ℝ := fun m => 1 /
    (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 4
  let g := Real.zeroBasedShiftedInverseFourthTerm
    (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a) (2 * Real.pi)
  have hresidual := Complex.logarithmicPhaseFiniteLeftProtectedResidual_pos
    t ht a ha
  have hgNonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    unfold g
    unfold Real.zeroBasedShiftedInverseFourthTerm
    have hbase := add_nonneg hresidual.le
      (mul_nonneg Complex.two_mul_pi_pos.le (Nat.cast_nonneg n))
    exact div_nonneg zero_le_one (pow_nonneg hbase 4)
  have hsum := Finset.sum_protected_inverse_power_le_tsum modes f g
    Complex.logarithmicPhaseFiniteLeftProtectedIndex
    (Complex.logarithmicPhaseFiniteLeftProtectedIndex_injective
      t ht a b ha hab)
    (fun m => le_of_eq
      (Complex.finiteLeftProtected_inverseFourth_eq_zeroBasedTerm
        t ht a b ha hab m))
    hgNonneg
    (Real.summable_zeroBasedShiftedInverseFourthTerm
      _ _ hresidual Complex.two_mul_pi_pos)
  exact le_trans hsum
    (Real.tsum_zeroBasedShiftedInverseFourthTerm_le_budget
      _ _ hresidual Complex.two_mul_pi_pos)

theorem Complex.sum_finiteRightProtected_inverseCube_le_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
      1 / (Complex.logarithmicPhaseRightInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 3) ≤
      Real.zeroBasedShiftedInverseCubeBudget
        (Complex.logarithmicPhaseFiniteRightProtectedResidual t b)
        (2 * Real.pi) := by
  let modes := Complex.logarithmicPhasePoissonRightInactiveModes t a b
  let f : ℤ → ℝ := fun m => 1 /
    (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 3
  let g := Real.zeroBasedShiftedInverseCubeTerm
    (Complex.logarithmicPhaseFiniteRightProtectedResidual t b) (2 * Real.pi)
  have hresidual := Complex.logarithmicPhaseFiniteRightProtectedResidual_pos
    t ht a b ha hab
  have hgNonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    unfold g
    unfold Real.zeroBasedShiftedInverseCubeTerm
    have hbase := add_nonneg hresidual.le
      (mul_nonneg Complex.two_mul_pi_pos.le (Nat.cast_nonneg n))
    exact div_nonneg zero_le_one (pow_nonneg hbase 3)
  have hsum := Finset.sum_protected_inverse_power_le_tsum modes f g
    Complex.logarithmicPhaseFiniteRightProtectedIndex
    (Complex.logarithmicPhaseFiniteRightProtectedIndex_injective
      t ht a b ha hab)
    (fun m => le_of_eq
      (Complex.finiteRightProtected_inverseCube_eq_zeroBasedTerm
        t ht a b ha hab m))
    hgNonneg
    (Real.summable_zeroBasedShiftedInverseCubeTerm
      _ _ hresidual Complex.two_mul_pi_pos)
  exact le_trans hsum
    (Real.tsum_zeroBasedShiftedInverseCubeTerm_le_budget
      _ _ hresidual Complex.two_mul_pi_pos)

theorem Complex.sum_finiteRightProtected_inverseFourth_le_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
      1 / (Complex.logarithmicPhaseRightInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 4) ≤
      Real.zeroBasedShiftedInverseFourthBudget
        (Complex.logarithmicPhaseFiniteRightProtectedResidual t b)
        (2 * Real.pi) := by
  let modes := Complex.logarithmicPhasePoissonRightInactiveModes t a b
  let f : ℤ → ℝ := fun m => 1 /
    (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 4
  let g := Real.zeroBasedShiftedInverseFourthTerm
    (Complex.logarithmicPhaseFiniteRightProtectedResidual t b) (2 * Real.pi)
  have hresidual := Complex.logarithmicPhaseFiniteRightProtectedResidual_pos
    t ht a b ha hab
  have hgNonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    unfold g
    unfold Real.zeroBasedShiftedInverseFourthTerm
    have hbase := add_nonneg hresidual.le
      (mul_nonneg Complex.two_mul_pi_pos.le (Nat.cast_nonneg n))
    exact div_nonneg zero_le_one (pow_nonneg hbase 4)
  have hsum := Finset.sum_protected_inverse_power_le_tsum modes f g
    Complex.logarithmicPhaseFiniteRightProtectedIndex
    (Complex.logarithmicPhaseFiniteRightProtectedIndex_injective
      t ht a b ha hab)
    (fun m => le_of_eq
      (Complex.finiteRightProtected_inverseFourth_eq_zeroBasedTerm
        t ht a b ha hab m))
    hgNonneg
    (Real.summable_zeroBasedShiftedInverseFourthTerm
      _ _ hresidual Complex.two_mul_pi_pos)
  exact le_trans hsum
    (Real.tsum_zeroBasedShiftedInverseFourthTerm_le_budget
      _ _ hresidual Complex.two_mul_pi_pos)

def Complex.logarithmicPhaseFiniteLeftProtectedSeriesBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedSquareCoefficient *
      Real.zeroBasedShiftedInverseSquareBudget
        (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a) (2 * Real.pi) +
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
      Real.zeroBasedShiftedInverseCubeBudget
        (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a) (2 * Real.pi) +
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
      Real.zeroBasedShiftedInverseCubeBudget
        (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a) (2 * Real.pi) +
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
      Real.zeroBasedShiftedInverseFourthBudget
        (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a) (2 * Real.pi)

def Complex.logarithmicPhaseFiniteRightProtectedSeriesBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedSquareCoefficient *
      Real.zeroBasedShiftedInverseSquareBudget
        (Complex.logarithmicPhaseFiniteRightProtectedResidual t b) (2 * Real.pi) +
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
      Real.zeroBasedShiftedInverseCubeBudget
        (Complex.logarithmicPhaseFiniteRightProtectedResidual t b) (2 * Real.pi) +
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
      Real.zeroBasedShiftedInverseCubeBudget
        (Complex.logarithmicPhaseFiniteRightProtectedResidual t b) (2 * Real.pi) +
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
      Real.zeroBasedShiftedInverseFourthBudget
        (Complex.logarithmicPhaseFiniteRightProtectedResidual t b) (2 * Real.pi)

theorem Complex.logarithmicPhaseFiniteLeftProtectedSeriesBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteLeftProtectedSeriesBudget t a b := by
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hresidual :=
    (Complex.logarithmicPhaseFiniteLeftProtectedResidual_pos t ht a ha).le
  have hsquare := Real.zeroBasedShiftedInverseSquareBudget_nonneg
    _ _ hresidual Complex.two_mul_pi_pos.le
  have hcube := Real.zeroBasedShiftedInverseCubeBudget_nonneg
    _ _ hresidual Complex.two_mul_pi_pos.le
  have hfourth := Real.zeroBasedShiftedInverseFourthBudget_nonneg
    _ _ hresidual Complex.two_mul_pi_pos.le
  unfold Complex.logarithmicPhaseFiniteLeftProtectedSeriesBudget
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (mul_nonneg Complex.logarithmicPhaseAdaptedSquareCoefficient_nonneg hsquare)
        (mul_nonneg
          (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient_nonneg
            t a hleft) hcube))
      (mul_nonneg
        (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient_nonneg
          t a b hab hleft) hcube))
    (mul_nonneg
      (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient_nonneg
        t a b hab hleft) hfourth)

theorem Complex.logarithmicPhaseFiniteRightProtectedSeriesBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteRightProtectedSeriesBudget t a b := by
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hresidual :=
    (Complex.logarithmicPhaseFiniteRightProtectedResidual_pos
      t ht a b ha hab).le
  have hsquare := Real.zeroBasedShiftedInverseSquareBudget_nonneg
    _ _ hresidual Complex.two_mul_pi_pos.le
  have hcube := Real.zeroBasedShiftedInverseCubeBudget_nonneg
    _ _ hresidual Complex.two_mul_pi_pos.le
  have hfourth := Real.zeroBasedShiftedInverseFourthBudget_nonneg
    _ _ hresidual Complex.two_mul_pi_pos.le
  unfold Complex.logarithmicPhaseFiniteRightProtectedSeriesBudget
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (mul_nonneg Complex.logarithmicPhaseAdaptedSquareCoefficient_nonneg hsquare)
        (mul_nonneg
          (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient_nonneg
            t a hleft) hcube))
      (mul_nonneg
        (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient_nonneg
          t a b hab hleft) hcube))
    (mul_nonneg
      (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient_nonneg
        t a b hab hleft) hfourth)

theorem Complex.sum_finiteLeft_closedMajorant_le_protectedSeriesBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (Complex.logarithmicPhaseLeftInactiveGap t m
          (Complex.logarithmicPhaseQuantitativeSupportLeft a))) ≤
      Complex.logarithmicPhaseFiniteLeftProtectedSeriesBudget t a b := by
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hbound := Complex.sum_adaptedClosedMajorant_le_fourPowerBudget
    t a b
    (Complex.logarithmicPhasePoissonLeftInactiveModes t a b)
    (fun m => Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a))
    (Real.zeroBasedShiftedInverseSquareBudget
      (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a) (2 * Real.pi))
    (Real.zeroBasedShiftedInverseCubeBudget
      (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a) (2 * Real.pi))
    (Real.zeroBasedShiftedInverseFourthBudget
      (Complex.logarithmicPhaseFiniteLeftProtectedResidual t a) (2 * Real.pi))
    hleft hab
    (Complex.sum_finiteLeftProtected_inverseSquare_le_budget
      t ht a b ha hab)
    (Complex.sum_finiteLeftProtected_inverseCube_le_budget
      t ht a b ha hab)
    (Complex.sum_finiteLeftProtected_inverseFourth_le_budget
      t ht a b ha hab)
  unfold Complex.logarithmicPhaseFiniteLeftProtectedSeriesBudget
  exact hbound

theorem Complex.sum_finiteRight_closedMajorant_le_protectedSeriesBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (Complex.logarithmicPhaseRightInactiveGap t m
          (Complex.logarithmicPhaseQuantitativeSupportRight b))) ≤
      Complex.logarithmicPhaseFiniteRightProtectedSeriesBudget t a b := by
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hbound := Complex.sum_adaptedClosedMajorant_le_fourPowerBudget
    t a b
    (Complex.logarithmicPhasePoissonRightInactiveModes t a b)
    (fun m => Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b))
    (Real.zeroBasedShiftedInverseSquareBudget
      (Complex.logarithmicPhaseFiniteRightProtectedResidual t b) (2 * Real.pi))
    (Real.zeroBasedShiftedInverseCubeBudget
      (Complex.logarithmicPhaseFiniteRightProtectedResidual t b) (2 * Real.pi))
    (Real.zeroBasedShiftedInverseFourthBudget
      (Complex.logarithmicPhaseFiniteRightProtectedResidual t b) (2 * Real.pi))
    hleft hab
    (Complex.sum_finiteRightProtected_inverseSquare_le_budget
      t ht a b ha hab)
    (Complex.sum_finiteRightProtected_inverseCube_le_budget
      t ht a b ha hab)
    (Complex.sum_finiteRightProtected_inverseFourth_le_budget
      t ht a b ha hab)
  unfold Complex.logarithmicPhaseFiniteRightProtectedSeriesBudget
  exact hbound

theorem Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_le_protectedSeriesBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b ≤
      Complex.logarithmicPhaseFiniteLeftProtectedSeriesBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
  have hpacket := Finset.sum_le_sum (fun m hm => by
    have hgap := Complex.logarithmicPhaseLeftInactiveGap_ge_curvature_third
      t ht a b ha hab hm
    have hgapPos := lt_of_lt_of_le
      (Complex.logarithmicPhaseFiniteLeftInactiveGap_pos t ht a ha) hgap
    have hstrict :
        ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a <
          2 * Real.pi * (-(m : ℝ)) := sub_pos.mp hgapPos
    have hcanonical := Complex.norm_logarithmicPhaseLeftInactiveModePacket_le
      t a b m ha hab hstrict
    unfold Complex.logarithmicPhaseLeftInactiveClosedMajorant at hcanonical
    have hparameter :=
      Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_eq_norm_parameter_of_nonneg
        t ht_nonneg a b m
    exact Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          Complex.logarithmicPhaseAdaptedClosedMajorant t a b
            (Complex.logarithmicPhaseLeftInactiveGap t m
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)))
      hparameter.symm hcanonical)
  exact le_trans hpacket
    (Complex.sum_finiteLeft_closedMajorant_le_protectedSeriesBudget
      t ht a b ha hab)

theorem Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_le_protectedSeriesBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b ≤
      Complex.logarithmicPhaseFiniteRightProtectedSeriesBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
  have hpacket := Finset.sum_le_sum (fun m hm => by
    have hgap := Complex.logarithmicPhaseRightInactiveGap_ge_curvature_third
      t ht a b ha hab hm
    have hgapPos := lt_of_lt_of_le
      (Complex.logarithmicPhaseFiniteRightInactiveGap_pos
        t ht a b ha hab) hgap
    have hstrict :
        2 * Real.pi * (-(m : ℝ)) <
          ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b :=
      sub_pos.mp hgapPos
    have hcanonical := Complex.norm_logarithmicPhaseRightInactiveModePacket_le
      t a b m ha hab hstrict
    unfold Complex.logarithmicPhaseRightInactiveClosedMajorant at hcanonical
    have hparameter :=
      Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_eq_norm_parameter_of_nonneg
        t ht_nonneg a b m
    exact Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          Complex.logarithmicPhaseAdaptedClosedMajorant t a b
            (Complex.logarithmicPhaseRightInactiveGap t m
              (Complex.logarithmicPhaseQuantitativeSupportRight b)))
      hparameter.symm hcanonical)
  exact le_trans hpacket
    (Complex.sum_finiteRight_closedMajorant_le_protectedSeriesBudget
      t ht a b ha hab)

end

end LFunctions
end Boundary
