import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.Owner

/-!
# Boundary transport inputs for pole-cleared zeta

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.EulerContinuationTransport.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The reflected left-edge pole-clearing denominator is `-z`. -/
theorem one_sub_sub_one_eq_neg_for_boundaryTransport
    (z : ℂ) :
    (((1 : ℂ) - z) - 1) = -z := by
  calc
    (((1 : ℂ) - z) - 1) = (((1 : ℂ) - z) + (-1 : ℂ)) := by
      exact sub_eq_add_neg ((1 : ℂ) - z) 1
    _ = (((1 : ℂ) + (-z)) + (-1 : ℂ)) := by
      exact congrArg (fun w : ℂ => w + (-1 : ℂ))
        (sub_eq_add_neg (1 : ℂ) z)
    _ = (1 : ℂ) + ((-z) + (-1 : ℂ)) := by
      exact add_assoc (1 : ℂ) (-z) (-1 : ℂ)
    _ = (1 : ℂ) + ((-1 : ℂ) + (-z)) := by
      exact congrArg (fun w : ℂ => (1 : ℂ) + w)
        (add_comm (-z) (-1 : ℂ))
    _ = ((1 : ℂ) + (-1 : ℂ)) + (-z) := by
      exact (add_assoc (1 : ℂ) (-1 : ℂ) (-z)).symm
    _ = 0 + (-z) := by
      exact congrArg (fun w : ℂ => w + (-z))
        (add_neg_cancel (1 : ℂ))
    _ = -z := by
      exact zero_add (-z)

/-- A real `1+1` spelling used to keep transport estimates explicit. -/
theorem boundaryTransport_real_one_add_one_eq_two :
    (1 : ℝ) + 1 = 2 := by
  exact one_add_one_eq_two

/-- Raising a real base above `2` dominates one additive copy of the base. -/
theorem boundaryTransport_one_add_le_sq_of_two_le
    {H : ℝ}
    (hH : (2 : ℝ) ≤ H) :
    1 + H ≤ H ^ (2 : ℕ) := by
  have hone_le_H : (1 : ℝ) ≤ H :=
    le_trans one_le_two hH
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hone_le_H
  have hone_add_le_twoH : 1 + H ≤ H + H :=
    add_le_add_right hone_le_H H
  have htwoH_le_HmulH : H + H ≤ H * H := by
    calc
      H + H = 2 * H := by
        exact (two_mul H).symm
      _ ≤ H * H := by
        exact mul_le_mul_of_nonneg_right hH hH_nonneg
  calc
    1 + H ≤ H + H := hone_add_le_twoH
    _ ≤ H * H := htwoH_le_HmulH
    _ = H ^ (2 : ℕ) := by
      exact (pow_two H).symm

/-- Negating the reflected pole-clearing denominator recovers `z`. -/
theorem neg_one_sub_sub_one_eq_self_for_boundaryTransport
    (z : ℂ) :
    -(((1 : ℂ) - z) - 1) = z := by
  calc
    -(((1 : ℂ) - z) - 1) = -(-z) := by
      exact congrArg Neg.neg (one_sub_sub_one_eq_neg_for_boundaryTransport z)
    _ = z := by
      exact neg_neg z

/-- Inserting the nonzero reflected pole-clearing denominator preserves the factor. -/
theorem boundaryTransport_insert_neg_denominator
    {z : ℂ}
    (h_ne : (-z : ℂ) ≠ 0) :
    (z - 1) = ((z - 1) / (-z)) * (-z) := by
  exact (div_mul_cancel₀ (z - 1) h_ne).symm

theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_ownerPrimitive :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact riemannZeta_poleCleared_boundaryLine_one_growth_bound_standard

/-- The reflected `re = 1` pole-cleared zeta factor has finite-order vertical growth.

This is the exact analytic input left after unfolding the completed functional equation in
the raw zeta variable.  The map `z ↦ 1-z` sends `re z = 0` to `re = 1`, so this is not a
consequence of the already-proved far-right Dirichlet-series boundary theorem at `re = 2`.
-/
theorem riemannZeta_reflected_leftBoundary_poleCleared_growth_bound_ownerPrimitive :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        boundaryLineOneVerticalTruncationHypotheses ((1 : ℂ) - z) →
        ‖(((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match riemannZeta_poleCleared_boundaryLine_one_growth_bound_ownerPrimitive with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      exact
        ⟨A, B, 2 * m, hA, hB,
          fun z hz_re hz_im htrunc =>
          let w : ℂ := (1 : ℂ) - z
          have hw_re : w.re = 1 :=
            one_sub_leftBoundary_re_eq_one hz_re
          have hw_im_norm : ‖w.im‖ = ‖z.im‖ := by
            have him_eq : w.im = -z.im := by
              calc
                w.im = (1 : ℂ).im - z.im := by
                  exact Complex.sub_im (1 : ℂ) z
                _ = 0 - z.im := by
                  exact congrArg (fun x : ℝ => x - z.im) Complex.one_im
                _ = -z.im := by
                  exact zero_sub z.im
            calc
              ‖w.im‖ = ‖-z.im‖ := by exact congrArg norm him_eq
              _ = ‖z.im‖ := norm_neg z.im
          have hw_im : 1 ≤ ‖w.im‖ :=
            Eq.subst (motive := fun x : ℝ => 1 ≤ x) hw_im_norm.symm hz_im
          have hw_norm_le : ‖w‖ ≤ 1 + ‖z‖ := by
            calc
              ‖w‖ = ‖(1 : ℂ) - z‖ := rfl
              _ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le (1 : ℂ) z
              _ = 1 + ‖z‖ := by
                exact congrArg (fun x : ℝ => x + ‖z‖) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
          have hbase_le : 1 + ‖w‖ ≤ (1 + ‖z‖) ^ (2 : ℕ) := by
            let H : ℝ := 1 + ‖z‖
            have hH_ge_one : (1 : ℝ) ≤ H :=
              le_add_of_nonneg_right (norm_nonneg z)
            have hleft_le : 1 + ‖w‖ ≤ 1 + (1 + ‖z‖) :=
              add_le_add_left hw_norm_le 1
            have htwoH_le_Hsq : 1 + (1 + ‖z‖) ≤ H ^ (2 : ℕ) := by
              have hH_ge_two : 2 ≤ H := by
                have hone_le_im : 1 ≤ ‖z.im‖ := hz_im
                have htwo_le_one_add_im : 2 ≤ 1 + ‖z.im‖ := by
                  calc
                    (2 : ℝ) = 1 + 1 := by
                      exact boundaryTransport_real_one_add_one_eq_two.symm
                    _ ≤ 1 + ‖z.im‖ := by
                      exact add_le_add_left hone_le_im 1
                calc (2 : ℝ) ≤ 1 + ‖z.im‖ := htwo_le_one_add_im
                  _ ≤ 1 + ‖z‖ := add_le_add_left (Complex.abs_im_le_abs z) 1
                  _ = H := rfl
              calc
                1 + (1 + ‖z‖) = 1 + H := rfl
                _ ≤ H ^ 2 := by exact boundaryTransport_one_add_le_sq_of_two_le hH_ge_two
                _ = H ^ (2 : ℕ) := rfl
            exact le_trans hleft_le htwoH_le_Hsq
          have hpow_le : (1 + ‖w‖) ^ m ≤ (1 + ‖z‖) ^ (2 * m) := by
            have hleft_nonneg : 0 ≤ 1 + ‖w‖ :=
              le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w))
            have hpow_base :
                (1 + ‖w‖) ^ m ≤ ((1 + ‖z‖) ^ (2 : ℕ)) ^ m :=
              pow_le_pow_left₀ hleft_nonneg hbase_le m
            have htarget_ge :
                ((1 + ‖z‖) ^ (2 : ℕ)) ^ m = (1 + ‖z‖) ^ (2 * m) := by
              exact (pow_mul (1 + ‖z‖) 2 m).symm
            exact hpow_base.trans_eq htarget_ge
          have hexp_le :
              Real.exp (B * (1 + ‖w‖) ^ m) ≤
                Real.exp (B * (1 + ‖z‖) ^ (2 * m)) := by
            exact Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left hpow_le (le_of_lt hB))
          le_trans (hbound w hw_re hw_im htrunc)
            (mul_le_mul_of_nonneg_left hexp_le (le_of_lt hA))⟩

/-- Functional-equation algebra for the left-edge pole-cleared zeta factor. -/
theorem riemannZeta_leftBoundary_completedFunctionalEquation_factorization
    {z : ℂ}
    (hz_re : z.re = 0)
    (hz_im : 1 ≤ ‖z.im‖) :
    (z - 1) * riemannZeta z =
      (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) := by
  match Gammaℝ_leftBoundary_nonzero_of_verticalTail hz_re hz_im with
  | ⟨hz_ne_zero, hone_sub_ne_zero, hGamma_ne, hGamma_reflected_ne⟩ =>
        have hw_ne_zero : ((1 : ℂ) - z) ≠ 0 := hone_sub_ne_zero
        have hw_minus_one_ne_zero : ((1 : ℂ) - z) - 1 ≠ 0 :=
          fun h =>
            have hz_zero : z = 0 := by
              calc
                z = -(((1 : ℂ) - z) - 1) := by
                  exact (neg_one_sub_sub_one_eq_self_for_boundaryTransport z).symm
                _ = -0 := by exact congrArg Neg.neg h
                _ = 0 := by exact neg_zero
            hz_ne_zero hz_zero
        have hGamma_factor :
            completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z := by
          have hζ := riemannZeta_def_of_ne_zero (s := z) hz_ne_zero
          have hmul := congrArg (fun x : ℂ => x * Complex.Gammaℝ z) hζ
          have hcancel :
              (completedRiemannZeta z / Complex.Gammaℝ z) * Complex.Gammaℝ z =
                completedRiemannZeta z := by
            exact div_mul_cancel₀ _ hGamma_ne
          exact (hmul.trans hcancel).symm
        have hcompleted_symm :
            completedRiemannZeta z = completedRiemannZeta ((1 : ℂ) - z) := by
          exact (completedRiemannZeta_one_sub z).symm
        have hzeta_z :
            riemannZeta z =
              riemannZeta ((1 : ℂ) - z) *
                (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
          have hζw := riemannZeta_def_of_ne_zero (s := ((1 : ℂ) - z)) hw_ne_zero
          calc
            riemannZeta z =
                completedRiemannZeta z / Complex.Gammaℝ z := by
              exact riemannZeta_def_of_ne_zero hz_ne_zero
            _ = completedRiemannZeta ((1 : ℂ) - z) / Complex.Gammaℝ z := by
              exact congrArg (fun x : ℂ => x / Complex.Gammaℝ z) hcompleted_symm
            _ = (riemannZeta ((1 : ℂ) - z) * Complex.Gammaℝ ((1 : ℂ) - z)) /
                Complex.Gammaℝ z := by
              have hζw_mul := congrArg
                (fun x : ℂ => x * Complex.Gammaℝ ((1 : ℂ) - z)) hζw
              have hζw_completed :
                  riemannZeta ((1 : ℂ) - z) * Complex.Gammaℝ ((1 : ℂ) - z) =
                    completedRiemannZeta ((1 : ℂ) - z) := by
                exact hζw_mul.trans (div_mul_cancel₀ _ hGamma_reflected_ne)
              exact congrArg (fun x : ℂ => x / Complex.Gammaℝ z) hζw_completed.symm
            _ = riemannZeta ((1 : ℂ) - z) *
                (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
              exact _root_.mul_div_assoc
                (riemannZeta ((1 : ℂ) - z))
                (Complex.Gammaℝ ((1 : ℂ) - z))
                (Complex.Gammaℝ z)
        calc
          (z - 1) * riemannZeta z =
              (z - 1) *
                (riemannZeta ((1 : ℂ) - z) *
                  (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) := by
            exact congrArg (fun x : ℂ => (z - 1) * x) hzeta_z
          _ = (((z - 1) / (((1 : ℂ) - z) - 1)) *
                (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
              ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) := by
            show (z - 1) *
                (riemannZeta ((1 : ℂ) - z) *
                  (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) =
              (((z - 1) / (((1 : ℂ) - z) - 1)) *
                (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
              ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z))
            have h_sub : ((1 : ℂ) - z) - 1 = -z :=
              one_sub_sub_one_eq_neg_for_boundaryTransport z
            have h_assoc :
                (z - 1) *
                    (riemannZeta ((1 : ℂ) - z) *
                      (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) =
                  (z - 1) * riemannZeta ((1 : ℂ) - z) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) :=
              (mul_assoc (z - 1) _ _).symm
            have h_insert :
                (z - 1) * riemannZeta ((1 : ℂ) - z) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) =
                  (((z - 1) / (-z)) * (-z)) * riemannZeta ((1 : ℂ) - z) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
              have h_left : (z - 1) * riemannZeta ((1 : ℂ) - z) =
                  (((z - 1) / (-z)) * (-z)) * riemannZeta ((1 : ℂ) - z) := by
                have h_ne : (-z : ℂ) ≠ 0 := by
                  exact fun hzero =>
                    hw_minus_one_ne_zero (h_sub.trans hzero)
                exact congrArg
                  (fun x : ℂ => x * riemannZeta ((1 : ℂ) - z))
                  (boundaryTransport_insert_neg_denominator h_ne)
              exact congrArg
                (fun x : ℂ => x * (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z))
                h_left
            have h_denominator :
                (((z - 1) / (-z)) * (-z)) * riemannZeta ((1 : ℂ) - z) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) =
                  (((z - 1) / (((1 : ℂ) - z) - 1)) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
                    ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) := by
              have h_neg :
                  (((z - 1) / (-z)) * (-z)) * riemannZeta ((1 : ℂ) - z) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) =
                    (((z - 1) / (-z)) *
                      (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
                    ((-z) * riemannZeta ((1 : ℂ) - z)) := by
                let A : ℂ := (z - 1) / (-z)
                let D : ℂ := -z
                let R : ℂ := riemannZeta ((1 : ℂ) - z)
                let G : ℂ := Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z
                have h₁ : ((A * D) * R) * G = (A * D) * (R * G) :=
                  mul_assoc (A * D) R G
                have h₂ : (A * D) * (R * G) = A * (D * (R * G)) :=
                  mul_assoc A D (R * G)
                have h₃ : A * (D * (R * G)) = A * ((D * R) * G) :=
                  congrArg (fun x : ℂ => A * x) (mul_assoc D R G).symm
                have h₄ : A * ((D * R) * G) = A * (G * (D * R)) :=
                  congrArg (fun x : ℂ => A * x) (mul_comm (D * R) G)
                have h₅ : A * (G * (D * R)) = (A * G) * (D * R) :=
                  (mul_assoc A G (D * R)).symm
                exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
              exact Eq.subst
                (motive := fun d : ℂ =>
                  (((z - 1) / (-z)) * (-z)) * riemannZeta ((1 : ℂ) - z) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) =
                    (((z - 1) / d) *
                      (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
                    (d * riemannZeta ((1 : ℂ) - z)))
                h_sub.symm
                h_neg
            exact h_assoc.trans (h_insert.trans h_denominator)

/-- Left-edge transport for the pole-cleared zeta factor through the completed functional
equation before the removable-pole normalization is applied.

This is the remaining analytic component: reflect by
`completedRiemannZeta_one_sub`, use the peeled vertical-growth input on the reflected
line `re (1 - z) = 1`, and control the resulting Gamma/reflection multiplier by the
left-boundary Stirling-ratio estimate. -/
theorem riemannZeta_leftBoundary_completedFunctionalEquation_stirling_transport_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        boundaryLineOneVerticalTruncationHypotheses ((1 : ℂ) - z) →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match leftBoundary_finiteOrder_product_growth_bound_of_condition
      (fun z : ℂ => boundaryLineOneVerticalTruncationHypotheses ((1 : ℂ) - z))
      (Gammaℝ_leftBoundary_completedFunctionalEquation_multiplier_stirling_growth_bound hbranch)
      riemannZeta_reflected_leftBoundary_poleCleared_growth_bound_ownerPrimitive with
  | ⟨A, B, m, hA, hB, hproduct⟩ =>
    exact
      ⟨A, B, m, hA, hB,
        fun z hz_re hz_im htrunc =>
          have hfactor :
              (z - 1) * riemannZeta z =
                (((z - 1) / (((1 : ℂ) - z) - 1)) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
                  ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) :=
            riemannZeta_leftBoundary_completedFunctionalEquation_factorization hz_re hz_im
          have hnorm_factor :
              ‖(z - 1) * riemannZeta z‖ =
                ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ *
                  ‖(((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)‖ := by
            have hnorm_raw := congrArg norm hfactor
            have hnorm_product :
                ‖(((z - 1) / (((1 : ℂ) - z) - 1)) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
                  ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z))‖ =
                    ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
                        (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ *
                      ‖(((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)‖ := by
              exact norm_mul
                (((z - 1) / (((1 : ℂ) - z) - 1)) *
                  (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z))
                ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z))
            exact hnorm_raw.trans hnorm_product
          calc
            ‖(z - 1) * riemannZeta z‖ =
                ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ *
                  ‖(((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)‖ :=
              hnorm_factor
            _ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
              hproduct z hz_re hz_im htrunc⟩

/-- Left-edge transport for the pole-cleared zeta factor through the completed functional
equation and the available vertical-tail Gamma/Stirling control. -/
theorem poleClearedRiemannZeta_leftBoundary_completedFunctionalEquation_stirling_transport_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        boundaryLineOneVerticalTruncationHypotheses ((1 : ℂ) - z) →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match riemannZeta_leftBoundary_completedFunctionalEquation_stirling_transport_growth_bound hbranch with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
    exact
      ⟨A, B, m, hA, hB,
        fun z hz_re hz_im htrunc =>
          have hz_ne_one : z ≠ 1 :=
            fun hz_eq =>
              have hz_re_one : z.re = 1 := by
                calc
                  z.re = (1 : ℂ).re := by
                    exact congrArg Complex.re hz_eq
                  _ = 1 := by
                    exact Complex.one_re
              have hzero_eq_one : (0 : ℝ) = 1 := by
                calc
                  (0 : ℝ) = z.re := hz_re.symm
                  _ = 1 := hz_re_one
              absurd hzero_eq_one zero_ne_one
          have hpole :
              poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
            poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
          calc
            ‖poleClearedRiemannZeta z‖ = ‖(z - 1) * riemannZeta z‖ :=
              congrArg norm hpole
            _ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
              hbound z hz_re hz_im htrunc⟩

/-- Exact two-edge boundary-growth input for the pole-cleared zeta strip theorem.

This is the boundary-growth layer separated from the vertical-strip Phragmen-Lindelöf
application: the left edge is the functional-equation/Gamma side, and the right edge is
the Dirichlet-series side. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        boundaryLineOneVerticalTruncationHypotheses ((1 : ℂ) - z) →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact poleClearedRiemannZeta_leftBoundary_completedFunctionalEquation_stirling_transport_growth_bound
    hbranch

/-- On `2 ≤ re z`, subtracting the leading Dirichlet coefficient identifies `ζ z - 1`
with the honest Dirichlet tail starting at `n = 2`. -/
theorem riemannZeta_sub_one_eq_dirichletSeries_tail
    {z : ℂ}
    (hz : 2 ≤ z.re) :
    riemannZeta z - 1 =
      ∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℂ) ^ z) := by
  have h_one_lt_re : 1 < z.re :=
    lt_of_lt_of_le one_lt_two hz
  let f : ℕ → ℂ := fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) ^ z)
  have hsum : Summable f := by
    have hfull : Summable (fun n : ℕ => 1 / ((n : ℂ) ^ z)) :=
      (Complex.summable_one_div_nat_cpow (p := z)).mpr h_one_lt_re
    exact (summable_nat_add_iff
      (f := fun n : ℕ => 1 / ((n : ℂ) ^ z)) 1).mpr hfull
  have hzeta :
      riemannZeta z = ∑' n : ℕ, f n :=
    have hzeta_raw :
        riemannZeta z = ∑' n : ℕ, 1 / (((n : ℂ) + 1) ^ z) :=
      zeta_eq_tsum_one_div_nat_add_one_cpow h_one_lt_re
    have hseries_eq :
        (∑' n : ℕ, 1 / (((n : ℂ) + 1) ^ z)) = ∑' n : ℕ, f n := by
      exact tsum_congr
        (fun n : ℕ =>
          have hbase : ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℂ)) := by
            calc
              ((n : ℂ) + 1) = ((n : ℕ) : ℂ) + ((1 : ℕ) : ℂ) := by
                exact congrArg (fun w : ℂ => (n : ℂ) + w)
                  (Nat.cast_one.symm : (1 : ℂ) = ((1 : ℕ) : ℂ))
              _ = (((n + 1 : ℕ) : ℂ)) := by
                exact (Nat.cast_add n 1).symm
          congrArg (fun w : ℂ => (1 : ℂ) / (w ^ z)) hbase)
    hzeta_raw.trans hseries_eq
  have hsplit :
      (∑ n ∈ Finset.range 1, f n) + (∑' n : ℕ, f (n + 1)) =
        ∑' n : ℕ, f n :=
    sum_add_tsum_nat_add 1 hsum
  have hprefix :
      ∑ n ∈ Finset.range 1, f n = 1 := by
    calc
      (∑ n ∈ Finset.range 1, f n) = f 0 := by
        exact Finset.sum_range_one f
      _ = (1 : ℂ) / ((1 : ℂ) ^ z) := by
        have hbase : (((0 + 1 : ℕ) : ℂ)) = (1 : ℂ) := by
          calc
            (((0 + 1 : ℕ) : ℂ)) = ((1 : ℕ) : ℂ) := rfl
            _ = (1 : ℂ) := by
              exact Nat.cast_one
        exact congrArg (fun w : ℂ => (1 : ℂ) / (w ^ z)) hbase
      _ = 1 := by
        have hone : (1 : ℂ) ^ z = 1 :=
          Complex.one_cpow z
        calc
          (1 : ℂ) / ((1 : ℂ) ^ z) = (1 : ℂ) / 1 := by
            exact congrArg (fun w : ℂ => (1 : ℂ) / w) hone
          _ = 1 := by
            have h_div_one : (1 : ℂ) / 1 = 1 :=
              div_self one_ne_zero
            exact h_div_one
  have hone_add_tail_eq_zeta :
      1 + (∑' n : ℕ, f (n + 1)) = riemannZeta z := by
    calc
      1 + (∑' n : ℕ, f (n + 1)) =
          (∑ n ∈ Finset.range 1, f n) + (∑' n : ℕ, f (n + 1)) := by
            exact congrArg (fun x : ℂ => x + (∑' n : ℕ, f (n + 1))) hprefix.symm
      _ = ∑' n : ℕ, f n := hsplit
      _ = riemannZeta z := hzeta.symm
  have hzeta_eq_one_add_tail :
      riemannZeta z = 1 + (∑' n : ℕ, f (n + 1)) :=
    hone_add_tail_eq_zeta.symm
  calc
    riemannZeta z - 1 =
        (1 + (∑' n : ℕ, f (n + 1))) - 1 := by
          exact congrArg (fun w : ℂ => w - 1) hzeta_eq_one_add_tail
    _ = ∑' n : ℕ, f (n + 1) :=
          calc
            (1 + (∑' n : ℕ, f (n + 1))) - 1 =
                ((∑' n : ℕ, f (n + 1)) + 1) - 1 := by
              exact congrArg (fun x : ℂ => x - 1)
                (add_comm 1 (∑' n : ℕ, f (n + 1)))
            _ = ∑' n : ℕ, f (n + 1) := by
              exact add_sub_cancel_right (∑' n : ℕ, f (n + 1)) 1
    _ = ∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℂ) ^ z) := by
          exact tsum_congr
            (fun n : ℕ =>
              have hbase :
                  (((n + 1 + 1 : ℕ) : ℂ)) = ((n + 2 : ℕ) : ℂ) := by
                calc
                  (((n + 1 + 1 : ℕ) : ℂ)) = (((n + 1) + 1 : ℕ) : ℂ) := rfl
                  _ = ((n + (1 + 1) : ℕ) : ℂ) := by
                    exact congrArg (fun k : ℕ => ((k : ℕ) : ℂ))
                      (Nat.add_assoc n 1 1).symm
                  _ = ((n + 2 : ℕ) : ℂ) := by
                    exact congrArg (fun k : ℕ => ((n + k : ℕ) : ℂ))
                      (one_add_one_eq_two : (1 : ℕ) + 1 = 2)
              congrArg (fun w : ℂ => (1 : ℂ) / (w ^ z)) hbase)

/-- Uniform boundedness of the far-right Dirichlet-series tail.

This far-right standard analytic primitive is the zeta-side input for finite-order control
of the completed zero packet; analytically it is the comparison of
`∑_{n≥2} n^{-z}` with the convergent real p-series at exponent `2`. -/
theorem riemannZeta_farRightHalfPlane_dirichletSeries_tsum_tail_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖(∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℂ) ^ z))‖ ≤ A := by
  let g : ℕ → ℝ := fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℕ))
  have hg_summable : Summable g := by
    have hfull : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (2 : ℕ))) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    exact (summable_nat_add_iff
      (f := fun n : ℕ => 1 / ((n : ℝ) ^ (2 : ℕ))) 2).mpr hfull
  have hg_nonneg : ∀ n : ℕ, 0 ≤ g n :=
    fun n =>
      div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg (n + 2)) 2)
  exact
    ⟨(∑' n : ℕ, g n) + 1,
      add_pos_of_nonneg_of_pos (tsum_nonneg hg_nonneg) zero_lt_one,
      fun z hz =>
          let f : ℕ → ℂ := fun n : ℕ => 1 / (((n + 2 : ℕ) : ℂ) ^ z)
          have hz_one_lt : 1 < z.re :=
            lt_of_lt_of_le one_lt_two hz
          have hf_summable : Summable (fun n : ℕ => ‖f n‖) := by
            have hfull : Summable (fun n : ℕ => 1 / ((n : ℂ) ^ z)) :=
              (Complex.summable_one_div_nat_cpow (p := z)).mpr hz_one_lt
            have htail : Summable (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℂ) ^ z)) :=
              (summable_nat_add_iff
                (f := fun n : ℕ => 1 / ((n : ℂ) ^ z)) 2).mpr hfull
            exact htail.norm
          have hterm_le : ∀ n : ℕ, ‖f n‖ ≤ g n :=
            fun n => by
            have hn_nat_pos : 0 < n + 2 :=
              Nat.succ_pos (n + 1)
            have hn_real_pos : 0 < ((n + 2 : ℕ) : ℝ) :=
              Nat.cast_pos.mpr hn_nat_pos
            have hn_real_one_le : 1 ≤ ((n + 2 : ℕ) : ℝ) :=
              have hnat_le : (1 : ℕ) ≤ n + 2 :=
                Nat.succ_le_iff.mpr hn_nat_pos
              have hcast_le : ((1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) :=
                Nat.cast_le.mpr hnat_le
              Eq.subst
                (motive := fun x : ℝ => x ≤ ((n + 2 : ℕ) : ℝ))
                Nat.cast_one
                hcast_le
            have hnorm_cpow :
                ‖(((n + 2 : ℕ) : ℂ) ^ z)‖ =
                  ((n + 2 : ℕ) : ℝ) ^ z.re :=
              Complex.norm_natCast_cpow_of_pos hn_nat_pos z
            have hnorm_term :
                ‖f n‖ = 1 / (((n + 2 : ℕ) : ℝ) ^ z.re) := by
              calc
                ‖f n‖ = ‖(1 : ℂ)‖ / ‖(((n + 2 : ℕ) : ℂ) ^ z)‖ := by
                  exact norm_div (1 : ℂ) ((((n + 2 : ℕ) : ℂ) ^ z))
                _ = 1 / ‖(((n + 2 : ℕ) : ℂ) ^ z)‖ := by
                  exact congrArg
                    (fun x : ℝ => x / ‖(((n + 2 : ℕ) : ℂ) ^ z)‖)
                    (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
                _ = 1 / (((n + 2 : ℕ) : ℝ) ^ z.re) := by
                  exact congrArg (fun x : ℝ => 1 / x) hnorm_cpow
            have hpow_mono :
                ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤
                  ((n + 2 : ℕ) : ℝ) ^ z.re :=
              Real.rpow_le_rpow_of_exponent_le hn_real_one_le hz
            have hpow_two_pos : 0 < ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) :=
              Real.rpow_pos_of_pos hn_real_pos 2
            have hdiv_le :
                1 / (((n + 2 : ℕ) : ℝ) ^ z.re) ≤
                  1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) :=
              one_div_le_one_div_of_le hpow_two_pos hpow_mono
            have hg_eq :
                g n = 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) := by
              calc
                g n = 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℕ)) := rfl
                _ = 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) := by
                  exact congrArg
                    (fun x : ℝ => 1 / x)
                    (Real.rpow_natCast (((n + 2 : ℕ) : ℝ)) 2).symm
            exact Eq.subst
              (motive := fun x : ℝ => ‖f n‖ ≤ x)
              hg_eq.symm
              (Eq.subst
                (motive := fun x : ℝ => x ≤ 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)))
                hnorm_term.symm
                hdiv_le)
          have hnorm_tail :
              ‖∑' n : ℕ, f n‖ ≤ ∑' n : ℕ, ‖f n‖ :=
            norm_tsum_le_tsum_norm hf_summable
          have hnorms_le_g :
              (∑' n : ℕ, ‖f n‖) ≤ ∑' n : ℕ, g n :=
            tsum_le_tsum hterm_le hf_summable hg_summable
          have htail_le_g :
              ‖∑' n : ℕ, f n‖ ≤ ∑' n : ℕ, g n :=
            le_trans hnorm_tail hnorms_le_g
          le_trans htail_le_g (le_add_of_nonneg_right zero_le_one)⟩

/-- The Dirichlet series tail for `ζ` is uniformly bounded on `2 ≤ re z`. -/
theorem riemannZeta_farRightHalfPlane_dirichletSeries_tail_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖riemannZeta z - 1‖ ≤ A := by
  match riemannZeta_farRightHalfPlane_dirichletSeries_tsum_tail_bound with
  | ⟨A, hA, htail⟩ =>
    exact
      ⟨A, hA,
        fun z hz =>
          have hidentity :
              riemannZeta z - 1 =
                ∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℂ) ^ z) :=
            riemannZeta_sub_one_eq_dirichletSeries_tail hz
          Eq.subst
            (motive := fun w : ℂ => ‖w‖ ≤ A)
            hidentity.symm
            (htail z hz)⟩

/-- Adding back the leading `1` preserves far-right boundedness of `ζ`. -/
theorem riemannZeta_farRightHalfPlane_dirichletSeries_bound_of_tail_bound
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖riemannZeta z - 1‖ ≤ A) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖riemannZeta z‖ ≤ A := by
  match htail with
  | ⟨A, hA, htail_bound⟩ =>
    exact
      ⟨A + 1, add_pos hA zero_lt_one,
        fun z hz =>
          have hdecomp : riemannZeta z = (riemannZeta z - 1) + 1 :=
            (sub_add_cancel (riemannZeta z) 1).symm
          have htriangle :
              ‖riemannZeta z‖ ≤ ‖riemannZeta z - 1‖ + ‖(1 : ℂ)‖ :=
            Eq.subst
              (motive := fun w : ℂ => ‖w‖ ≤ ‖riemannZeta z - 1‖ + ‖(1 : ℂ)‖)
              hdecomp.symm
              (norm_add_le (riemannZeta z - 1) (1 : ℂ))
          have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) :=
            (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
          have hsum :
              ‖riemannZeta z - 1‖ + ‖(1 : ℂ)‖ ≤ A + 1 :=
            Eq.subst
              (motive := fun x : ℝ => ‖riemannZeta z - 1‖ + x ≤ A + 1)
              hone_norm.symm
              (add_le_add_right (htail_bound z hz) 1)
          le_trans htriangle hsum⟩

/-- The far-right half-plane Dirichlet-series bound for `ζ`. -/
theorem riemannZeta_farRightHalfPlane_dirichletSeries_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖riemannZeta z‖ ≤ A := by
  exact riemannZeta_farRightHalfPlane_dirichletSeries_bound_of_tail_bound
    riemannZeta_farRightHalfPlane_dirichletSeries_tail_bound

/-- On the right edge `re z = 2` of the critical strip, the pole-cleared zeta factor
has finite-order growth by the far-right Dirichlet-series bound. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_rightBoundary_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match riemannZeta_farRightHalfPlane_dirichletSeries_bound with
  | ⟨A, hA, hzeta_bound⟩ =>
    exact
      ⟨A, 1, 1, hA, zero_lt_one,
        fun z hz_re _hz_im =>
          let H : ℝ := 1 + ‖z‖
          have hH_ge_one : (1 : ℝ) ≤ H :=
            le_add_of_nonneg_right (norm_nonneg z)
          have hH_nonneg : 0 ≤ H :=
            le_trans zero_le_one hH_ge_one
          have hz_far : 2 ≤ z.re :=
            le_of_eq hz_re.symm
          have hzeta : ‖riemannZeta z‖ ≤ A :=
            hzeta_bound z hz_far
          have hsub_norm : ‖z - 1‖ ≤ H := by
            calc
              ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ :=
                norm_sub_le z (1 : ℂ)
              _ = ‖z‖ + 1 := by
                exact congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
              _ = H := by
                exact (add_comm ‖z‖ 1)
          have hproduct :
              ‖(z - 1) * riemannZeta z‖ ≤ H * A := by
            calc
              ‖(z - 1) * riemannZeta z‖ =
                  ‖z - 1‖ * ‖riemannZeta z‖ := by
                exact norm_mul (z - 1) (riemannZeta z)
              _ ≤ H * A :=
                mul_le_mul hsub_norm hzeta (norm_nonneg (riemannZeta z)) hH_nonneg
          have hH_le_expH : H ≤ Real.exp H :=
            le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp H)
          have hscaled :
              H * A ≤ A * Real.exp H := by
            calc
              H * A = A * H := by
                exact mul_comm H A
              _ ≤ A * Real.exp H :=
                mul_le_mul_of_nonneg_left hH_le_expH (le_of_lt hA)
          have hexponent :
              (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) = H := by
            calc
              (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) = (1 + ‖z‖) ^ (1 : ℕ) := by
                exact one_mul ((1 + ‖z‖) ^ (1 : ℕ))
              _ = 1 + ‖z‖ := by
                exact pow_one (1 + ‖z‖)
              _ = H := rfl
          le_trans hproduct
            (Eq.subst
              (motive := fun x : ℝ => H * A ≤ A * Real.exp x)
              hexponent.symm
              hscaled)⟩

/-- The right-edge estimate transfers to the removable pole-cleared zeta normalization.

The vertical edge `re z = 2` is disjoint from the pole face, so this is only the
definition-level transport from `(s - 1) ζ(s)` to `poleClearedRiemannZeta`. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match riemannZeta_rightCriticalStrip_poleCleared_rightBoundary_growth_bound with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
    exact
      ⟨A, B, m, hA, hB,
        fun z hz_re hz_im =>
          have hz_ne_one : z ≠ 1 :=
            fun hz_eq =>
              have hone_re : z.re = 1 := by
                calc
                  z.re = (1 : ℂ).re := by
                    exact congrArg Complex.re hz_eq
                  _ = 1 := by
                    exact Complex.one_re
              have htwo_eq_one : (2 : ℝ) = 1 := by
                calc
                  (2 : ℝ) = z.re := hz_re.symm
                  _ = 1 := hone_re
              absurd htwo_eq_one (show (2 : ℝ) ≠ 1 from ne_of_gt one_lt_two)
          have hpc :
              poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
            poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
          Eq.subst
            (motive := fun w : ℂ =>
              ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
            hpc.symm
            (hbound z hz_re hz_im)⟩

/-- Right-edge boundary growth for the pole-cleared zeta factor from the far-right
Dirichlet-series estimate. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_dirichletSeries_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_growth_bound

/-- Exact two-edge boundary-growth input for the pole-cleared zeta strip theorem.

This public owner theorem is a thin wrapper over the two mathematically distinct vertical
edge inputs: the left edge comes from the functional equation and Gamma control, while the
right edge comes from the Dirichlet-series estimate. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_verticalBoundary_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        boundaryLineOneVerticalTruncationHypotheses ((1 : ℂ) - z) →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
    (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  exact
    ⟨poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound
        hbranch,
      poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_dirichletSeries_growth_bound⟩

end
end LFunctions
end Boundary
