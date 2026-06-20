import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.Owner

/-!
# Jensen counting consumers for entire functions

This file consumes the owner-level Jensen formula API from
`Boundary.LFunctions.EntireJensenFormula` and derives finite-order counting
wrappers used by the completed-zeta zero side.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The real coercion of the numeral identity `1 + 2 = 3`. -/
private theorem real_one_add_two_eq_three :
    (1 : ℝ) + 2 = 3 := by
  calc
    (1 : ℝ) + 2 = 2 + 1 := by
      exact add_comm (1 : ℝ) 2
    _ = 3 := by
      exact two_add_one_eq_three

/-- Pointwise logarithmic control on the doubled circle from a finite-order bound. -/
theorem entireFunction_logOnCircle_bound_of_finiteOrder
    (F : ℂ → ℂ)
    (A B : ℝ) (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hfinite :
      ∀ z : ℂ,
        ‖F z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ M : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        ∀ z : ℂ,
          ‖z‖ = 2 * R →
          Real.log ‖F z‖ ≤ M + B * (1 + 2 * R) ^ m := by
  exact ⟨max 0 (Real.log A), fun R hR z hz_norm => by
    let E : ℝ := B * (1 + 2 * R) ^ m
    have hR_nonneg : 0 ≤ R :=
      le_trans zero_le_one hR
    have htwoR_nonneg : 0 ≤ 2 * R :=
      mul_nonneg zero_le_two hR_nonneg
    have hbase_nonneg : 0 ≤ 1 + 2 * R :=
      add_nonneg zero_le_one htwoR_nonneg
    have hE_nonneg : 0 ≤ E :=
      mul_nonneg (le_of_lt hB) (pow_nonneg hbase_nonneg m)
    have htarget_nonneg : 0 ≤ max 0 (Real.log A) + E :=
      add_nonneg (le_max_left 0 (Real.log A)) hE_nonneg
    match eq_or_lt_of_le (norm_nonneg (F z)) with
    | Or.inl hzero =>
        calc
          Real.log ‖F z‖ = Real.log 0 := by
            exact congrArg Real.log hzero.symm
          _ = 0 := by
            exact Real.log_zero
          _ ≤ max 0 (Real.log A) + E := htarget_nonneg
    | Or.inr hpos =>
        have hfinite_z :
            ‖F z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
          hfinite z
        have hpow_arg :
            (1 + ‖z‖) ^ m = (1 + 2 * R) ^ m := by
          exact congrArg (fun x : ℝ => (1 + x) ^ m) hz_norm
        have hfinite_circle :
            ‖F z‖ ≤ A * Real.exp E := by
          exact Eq.subst
            (motive := fun x : ℝ => ‖F z‖ ≤ A * Real.exp (B * x))
            hpow_arg
            hfinite_z
        have h_exp_target :
            A * Real.exp E = Real.exp (Real.log A + E) := by
          calc
            A * Real.exp E = Real.exp (Real.log A) * Real.exp E := by
              exact congrArg (fun x : ℝ => x * Real.exp E) (Real.exp_log hA).symm
            _ = Real.exp (Real.log A + E) := by
              exact (Real.exp_add (Real.log A) E).symm
        have hlog_le_raw :
            Real.log ‖F z‖ ≤ Real.log A + E :=
          (Real.log_le_iff_le_exp hpos).mpr (hfinite_circle.trans_eq h_exp_target)
        have hlogA_le_max : Real.log A ≤ max 0 (Real.log A) :=
          le_max_right 0 (Real.log A)
        have htarget :
            Real.log A + E ≤ max 0 (Real.log A) + E :=
          add_le_add_right hlogA_le_max E
        exact le_trans hlog_le_raw htarget⟩

/-- Circlewise logarithmic control bounds the logarithmic maximum modulus. -/
theorem entireFunction_logMaxOnCircle_bound_of_logOnCircle
    (F : ℂ → ℂ)
    (B : ℝ) (m : ℕ)
    (M : ℝ)
    (hcircle :
      ∀ R : ℝ,
        1 ≤ R →
        ∀ z : ℂ,
          ‖z‖ = 2 * R →
          Real.log ‖F z‖ ≤ M + B * (1 + 2 * R) ^ m) :
    ∀ R : ℝ,
      1 ≤ R →
      entireFunctionLogMaxOnCircle F (2 * R) ≤
        M + B * (1 + 2 * R) ^ m := by
  intro R hR
  have hsup :
      sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = 2 * R ∧ x = Real.log ‖F z‖} ≤
        M + B * (1 + 2 * R) ^ m :=
    csSup_le
      ⟨Real.log ‖F (((2 * R : ℝ) : ℂ))‖,
        ⟨((2 * R : ℝ) : ℂ), by
          have hR_nonneg : 0 ≤ R := le_trans zero_le_one hR
          have htwoR_nonneg : 0 ≤ 2 * R := mul_nonneg zero_le_two hR_nonneg
          exact complex_norm_ofReal_of_nonnegative htwoR_nonneg, rfl⟩⟩
      (fun x hx =>
        match hx with
        | ⟨z, hz_norm, hx_eq⟩ =>
            Eq.subst
              (motive := fun y : ℝ => y ≤ M + B * (1 + 2 * R) ^ m)
              hx_eq.symm
              (hcircle R hR z hz_norm))
  have hlogMax_def :
      entireFunctionLogMaxOnCircle F (2 * R) =
        sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = 2 * R ∧ x = Real.log ‖F z‖} := by
    rfl
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ M + B * (1 + 2 * R) ^ m)
    hlogMax_def.symm
    hsup

/-- Finite-order growth controls the logarithmic maximum modulus on doubled circles. -/
theorem entireFunction_logMaxOnCircle_bound_of_finiteOrder
    (F : ℂ → ℂ)
    (A B : ℝ) (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hfinite :
      ∀ z : ℂ,
        ‖F z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ M : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionLogMaxOnCircle F (2 * R) ≤
          M + B * (1 + 2 * R) ^ m := by
  match entireFunction_logOnCircle_bound_of_finiteOrder F A B m hA hB hfinite with
  | ⟨M, hcircle⟩ =>
      exact ⟨M, entireFunction_logMaxOnCircle_bound_of_logOnCircle F B m M hcircle⟩

/-- Jensen's formula converts maximum-modulus control on the doubled circle into
closed-disk zero counting with analytic multiplicity.

This is the zero-ledger log-max wrapper.  The owner analytic primitive is
`entireFunctionZeroMultiplicityCounting_closedDisk_le_boundaryLogAverage`;
this theorem only exposes the downstream logarithmic-maximum formulation with
the standard doubled-radius `log 2` factor. -/
theorem entireFunctionZeroMultiplicityCounting_closedDisk_le_const_add_logMax_by_jensen
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ * entireFunctionLogMaxOnCircle F (2 * R) := by
  let hJensen :
      ∃ J : ℝ,
        ∀ R : ℝ,
          1 ≤ R →
          entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
            J + (Real.log 2)⁻¹ * entireFunctionLogMaxOnCircle F (2 * R) :=
    entireFunction_jensenFormula_zeroMultiplicityCounting_closedDisk_le_logMax
      F hF hnontrivial
  match hJensen with
  | ⟨J, hJ⟩ =>
      exact ⟨J, hJ⟩

/-- Jensen's formula plus a logarithmic maximum-modulus majorant gives the
logarithmic-radius zero-counting estimate.  The primitive is
`entireFunctionZeroMultiplicityCounting_closedDisk_le_boundaryLogAverage`
above; this theorem only exposes the downstream log-max formulation. -/
theorem entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen_of_logMax
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (B : ℝ) (m : ℕ)
    (_hB : 0 < B)
    (M : ℝ)
    (hlogMax :
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionLogMaxOnCircle F (2 * R) ≤
          M + B * (1 + 2 * R) ^ m) :
    ∃ J : ℝ, ∃ B' : ℝ,
      0 < B' ∧
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + B' * (1 + 2 * R) ^ m := by
  match entireFunctionZeroMultiplicityCounting_closedDisk_le_const_add_logMax_by_jensen
      F hF hnontrivial with
  | ⟨J₀, hjensen⟩ =>
      let c : ℝ := (Real.log 2)⁻¹
      exact ⟨J₀ + c * M, c * B, by
        have hlog_two_pos : 0 < c :=
          inv_pos.mpr (Real.log_pos one_lt_two)
        exact mul_pos hlog_two_pos _hB, fun R hR => by
        have hcount :
            entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
              J₀ + c * entireFunctionLogMaxOnCircle F (2 * R) :=
          hjensen R hR
        have hlog :
            entireFunctionLogMaxOnCircle F (2 * R) ≤
              M + B * (1 + 2 * R) ^ m :=
          hlogMax R hR
        have hlog_two_nonneg : 0 ≤ c :=
          le_of_lt (inv_pos.mpr (Real.log_pos one_lt_two))
        have hscaled_log :
            c * entireFunctionLogMaxOnCircle F (2 * R) ≤
              c * (M + B * (1 + 2 * R) ^ m) :=
          mul_le_mul_of_nonneg_left hlog hlog_two_nonneg
        have hwith_constant :
            J₀ + c * entireFunctionLogMaxOnCircle F (2 * R) ≤
              J₀ + c * (M + B * (1 + 2 * R) ^ m) :=
          add_le_add_left hscaled_log J₀
        have htarget :
            J₀ + c * (M + B * (1 + 2 * R) ^ m) =
              (J₀ + c * M) + (c * B) * (1 + 2 * R) ^ m := by
          show J₀ + c * (M + B * (1 + 2 * R) ^ m) = (J₀ + c * M) + (c * B) * (1 + 2 * R) ^ m
          calc
            J₀ + c * (M + B * (1 + 2 * R) ^ m)
                = J₀ + (c * M + c * (B * (1 + 2 * R) ^ m)) := by
              exact congrArg (fun x : ℝ => J₀ + x) (mul_add c M (B * (1 + 2 * R) ^ m))
            _ = J₀ + (c * M + (c * B) * (1 + 2 * R) ^ m) := by
              exact congrArg (fun x : ℝ => J₀ + (c * M + x))
                (mul_assoc c B ((1 + 2 * R) ^ m)).symm
            _ = (J₀ + c * M) + (c * B) * (1 + 2 * R) ^ m :=
              (add_assoc J₀ (c * M) ((c * B) * (1 + 2 * R) ^ m)).symm
        exact le_trans hcount (hwith_constant.trans_eq htarget)⟩

/-- Jensen formula plus finite-order growth gives the logarithmic-radius counting estimate.

This is the true analytic root for the generic entire-function zero-counting step:
Jensen's formula bounds the closed-disk zero count by a constant depending on the first
nonzero Taylor coefficient and by the finite-order majorant on a doubled circle. -/
theorem entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen_logarithmic
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (A B : ℝ) (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hfinite :
      ∀ z : ℂ,
        ‖F z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ J : ℝ,
    ∃ B' : ℝ,
      0 < B' ∧
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + B' * (1 + 2 * R) ^ m := by
  match entireFunction_logMaxOnCircle_bound_of_finiteOrder F A B m hA hB hfinite with
  | ⟨M, hlogMax⟩ =>
      exact entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen_of_logMax
        F hF hnontrivial B m hB M hlogMax

/-- The doubled affine radius is bounded by three times the radius for `R ≥ 1`. -/
theorem one_add_two_mul_le_three_mul_of_one_le
    {R : ℝ}
    (hR : 1 ≤ R) :
    1 + 2 * R ≤ 3 * R := by
  have hone_le_R : 1 ≤ R := hR
  calc
    1 + 2 * R ≤ R + 2 * R := by
      exact add_le_add_right hone_le_R (2 * R)
    _ = 3 * R := by
      show R + 2 * R = 3 * R
      calc R + 2 * R = 1 * R + 2 * R := by exact congrArg (· + 2 * R) (one_mul R).symm
        _ = (1 + 2) * R := (add_mul 1 2 R).symm
        _ = 3 * R := by exact congrArg (· * R) real_one_add_two_eq_three

/-- A logarithmic Jensen estimate with finite-order radius term gives polynomial
closed-disk zero counting. -/
theorem entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen_logarithmic_bound
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (B : ℝ) (m : ℕ)
    (hB : 0 < B)
    (J : ℝ)
    (hjensen :
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + B * (1 + 2 * R) ^ m) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          C * R ^ d := by
  exact ⟨(|J| + B * (3 : ℝ) ^ m) + 1, m, by
    have hJ_nonneg : 0 ≤ |J| := abs_nonneg J
    have hB_three_pos : 0 < B * (3 : ℝ) ^ m :=
      mul_pos hB (pow_pos zero_lt_three m)
    exact add_pos_of_nonneg_of_pos (add_nonneg hJ_nonneg (le_of_lt hB_three_pos)) zero_lt_one,
    fun R hR => by
      have hcount :
          entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
            J + B * (1 + 2 * R) ^ m :=
        hjensen R hR
      have hR_nonneg : 0 ≤ R :=
        le_trans zero_le_one hR
      have hthreeR_nonneg : 0 ≤ (3 : ℝ) * R :=
        mul_nonneg zero_le_three hR_nonneg
      have hradius_le : 1 + 2 * R ≤ (3 : ℝ) * R :=
        one_add_two_mul_le_three_mul_of_one_le hR
      have hpow_le :
          (1 + 2 * R) ^ m ≤ ((3 : ℝ) * R) ^ m :=
        pow_le_pow_left₀
          (by
            have htwoR_nonneg : 0 ≤ 2 * R := mul_nonneg zero_le_two hR_nonneg
            exact add_nonneg zero_le_one htwoR_nonneg)
          hradius_le
          m
      have hscaled_pow :
          B * (1 + 2 * R) ^ m ≤ B * (((3 : ℝ) * R) ^ m) :=
        mul_le_mul_of_nonneg_left hpow_le (le_of_lt hB)
      have hfactor :
          B * (((3 : ℝ) * R) ^ m) = (B * (3 : ℝ) ^ m) * R ^ m := by
        calc
          B * (((3 : ℝ) * R) ^ m) =
              B * ((3 : ℝ) ^ m * R ^ m) := by
            exact congrArg (fun x : ℝ => B * x) (mul_pow (3 : ℝ) R m)
          _ = (B * (3 : ℝ) ^ m) * R ^ m := by
            exact (mul_assoc B ((3 : ℝ) ^ m) (R ^ m)).symm
      have hfinite_part :
          J + B * (1 + 2 * R) ^ m ≤
            |J| + (B * (3 : ℝ) ^ m) * R ^ m := by
        have hJ_le_abs : J ≤ |J| := le_abs_self J
        exact add_le_add hJ_le_abs (hscaled_pow.trans_eq hfactor)
      have hRpow_ge_one : (1 : ℝ) ≤ R ^ m :=
        one_le_pow₀ hR
      have hJ_abs_mul :
          |J| ≤ |J| * R ^ m := by
        exact le_mul_of_one_le_right (abs_nonneg J) hRpow_ge_one
      have hcombine :
          |J| + (B * (3 : ℝ) ^ m) * R ^ m ≤
            (|J| + B * (3 : ℝ) ^ m) * R ^ m := by
        have hright :
            |J| * R ^ m + (B * (3 : ℝ) ^ m) * R ^ m =
              (|J| + B * (3 : ℝ) ^ m) * R ^ m :=
          (add_mul |J| (B * (3 : ℝ) ^ m) (R ^ m)).symm
        exact (add_le_add_right hJ_abs_mul ((B * (3 : ℝ) ^ m) * R ^ m)).trans_eq hright
      have hplus_one :
          (|J| + B * (3 : ℝ) ^ m) * R ^ m ≤
            ((|J| + B * (3 : ℝ) ^ m) + 1) * R ^ m := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right zero_le_one)
          (pow_nonneg hR_nonneg m)
      exact le_trans hcount (le_trans hfinite_part (le_trans hcombine hplus_one))⟩

/-- Jensen formula plus finite-order growth gives polynomial zero counting in closed disks.

The only analytic input is the logarithmic Jensen estimate; the final polynomial
majorization is elementary. -/
theorem entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen_formula
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (A B : ℝ) (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hfinite :
      ∀ z : ℂ,
        ‖F z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          C * R ^ d := by
  match entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen_logarithmic
      F hF hnontrivial A B m hA hB hfinite with
  | ⟨J, B', hB', hjensen⟩ =>
      exact entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen_logarithmic_bound
        F hF B' m hB' J hjensen

/-- Jensen finite-order counting theorem for nonzero entire functions.

This is the analytic owner theorem: a nontrivial entire function of exponential
finite order has polynomially bounded zero count in closed disks, counted with
analytic multiplicity. -/
theorem entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen_owner
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (A B : ℝ) (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hfinite :
      ∀ z : ℂ,
        ‖F z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          C * R ^ d := by
  exact entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen_formula
    F hF hnontrivial A B m hA hB hfinite

/-- Jensen finite-order counting theorem for nonzero entire functions.

This is the analytic owner theorem: a nontrivial entire function of exponential
finite order has polynomially bounded zero count in closed disks, counted with
analytic multiplicity. -/
theorem entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (hfinite :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖F z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          C * R ^ d := by
  match hfinite with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      exact
        entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen_owner
          F hF hnontrivial A B m hA hB hbound

end

end LFunctions
end Boundary
