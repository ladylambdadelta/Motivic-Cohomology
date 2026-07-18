import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.OwnerParts.Part06_CentralGrowth

/-!
# Pole-cleared zeta global finite-order assembly
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The first nonnegative summand is bounded by a three-term sum. -/
private theorem firstReal_le_threeSum
    (first second third : ℝ)
    (hsecond : 0 ≤ second)
    (hthird : 0 ≤ third) :
    first ≤ first + second + third :=
  le_trans
    (le_add_of_nonneg_right hsecond)
    (le_add_of_nonneg_right hthird)

/-- The middle nonnegative summand is bounded by a three-term sum. -/
private theorem middleReal_le_threeSum
    (first second third : ℝ)
    (hfirst : 0 ≤ first)
    (hthird : 0 ≤ third) :
    second ≤ first + second + third :=
  le_trans
    (le_add_of_nonneg_left hfirst)
    (le_add_of_nonneg_right hthird)

/-- The final nonnegative summand is bounded by a three-term sum. -/
private theorem finalReal_le_threeSum
    (first second third : ℝ)
    (hfirst : 0 ≤ first)
    (hsecond : 0 ≤ second) :
    third ≤ first + second + third := by
  have hthird_le_second_third : third ≤ second + third :=
    le_add_of_nonneg_left hsecond
  have hsecond_third_le_sum : second + third ≤ first + second + third := by
    have hinsert_first : second + third ≤ first + (second + third) :=
      le_add_of_nonneg_left hfirst
    exact hinsert_first.trans_eq (add_assoc first second third).symm
  exact le_trans hthird_le_second_third hsecond_third_le_sum

/-- Each degree is bounded by the three-term degree sum. -/
private theorem firstNat_le_threeSum (first second third : ℕ) :
    first ≤ first + second + third :=
  Eq.subst
    (motive := fun degree : ℕ => first ≤ degree)
    (Nat.add_assoc first second third).symm
    (Nat.le_add_right first (second + third))

private theorem middleNat_le_threeSum (first second third : ℕ) :
    second ≤ first + second + third :=
  le_trans (Nat.le_add_left second first)
    (Nat.le_add_right (first + second) third)

private theorem finalNat_le_threeSum (first second third : ℕ) :
    third ≤ first + second + third :=
  le_trans (Nat.le_add_left third second)
    (Eq.subst
      (motive := fun degree : ℕ => second + third ≤ degree)
      (Nat.add_assoc first second third).symm
      (Nat.le_add_left (second + third) first))

/-- Region selection for the global three-envelope patch. -/
private theorem poleClearedRiemannZeta_globalFiniteOrder_threeRegion_bound
    (Al Bl : ℝ) (ml : ℕ)
    (Ac Bc : ℝ) (mc : ℕ)
    (Ar Br : ℝ) (mr : ℕ)
    (hAl : 0 ≤ Al) (hBl : 0 ≤ Bl)
    (hAc : 0 ≤ Ac) (hBc : 0 ≤ Bc)
    (hAr : 0 ≤ Ar) (hBr : 0 ≤ Br)
    (hleft : ∀ z : ℂ, z.re ≤ 0 →
      ‖poleClearedRiemannZeta z‖ ≤ Al * Real.exp (Bl * (1 + ‖z‖) ^ ml))
    (hcentral : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 2 →
      ‖poleClearedRiemannZeta z‖ ≤ Ac * Real.exp (Bc * (1 + ‖z‖) ^ mc))
    (hright : ∀ z : ℂ, 2 ≤ z.re →
      ‖poleClearedRiemannZeta z‖ ≤ Ar * Real.exp (Br * (1 + ‖z‖) ^ mr))
    (z : ℂ) :
    ‖poleClearedRiemannZeta z‖ ≤
      (Al + Ac + Ar) *
        Real.exp ((Bl + Bc + Br) * (1 + ‖z‖) ^ (ml + mc + mr)) := by
  match le_total z.re 0 with
  | Or.inl hz_left =>
      exact le_trans (hleft z hz_left)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAl (firstReal_le_threeSum Al Ac Ar hAc hAr)
          (firstReal_le_threeSum Bl Bc Br hBc hBr) hBl
          (firstNat_le_threeSum ml mc mr))
  | Or.inr hz_nonnegative =>
      match le_total 2 z.re with
      | Or.inl hz_right =>
          exact le_trans (hright z hz_right)
            (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
              hAr (finalReal_le_threeSum Al Ac Ar hAl hAc)
              (finalReal_le_threeSum Bl Bc Br hBl hBc) hBr
              (finalNat_le_threeSum ml mc mr))
      | Or.inr hz_le_two =>
          exact le_trans (hcentral z hz_nonnegative hz_le_two)
            (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
              hAc (middleReal_le_threeSum Al Ac Ar hAl hAr)
              (middleReal_le_threeSum Bl Bc Br hBl hBr) hBc
              (middleNat_le_threeSum ml mc mr))

/-- Patch left, central, and right finite-order envelopes into a global envelope. -/
theorem poleClearedRiemannZeta_globalFiniteOrder_growth_of_left_central_right
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hcentral :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hleft with
  | ⟨Al, Bl, ml, hAl_pos, hBl_pos, hleft_bound⟩ =>
      match hcentral with
      | ⟨Ac, Bc, mc, hAc_pos, hBc_pos, hcentral_bound⟩ =>
          match hright with
          | ⟨Ar, Br, mr, hAr_pos, hBr_pos, hright_bound⟩ =>
              exact
                ⟨Al + Ac + Ar, Bl + Bc + Br, ml + mc + mr,
                  add_pos (add_pos hAl_pos hAc_pos) hAr_pos,
                  add_pos (add_pos hBl_pos hBc_pos) hBr_pos,
                  poleClearedRiemannZeta_globalFiniteOrder_threeRegion_bound
                    Al Bl ml Ac Bc mc Ar Br mr
                    (le_of_lt hAl_pos) (le_of_lt hBl_pos)
                    (le_of_lt hAc_pos) (le_of_lt hBc_pos)
                    (le_of_lt hAr_pos) (le_of_lt hBr_pos)
                    hleft_bound hcentral_bound hright_bound⟩

theorem poleClearedRiemannZeta_globalFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_globalFiniteOrder_growth_of_left_central_right
      (poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_from_functionalEquation
        hbranch
        (poleClearedRiemannZeta_reflectedRightHalfPlane_finiteOrder_growth_from_EulerMaclaurin
          hpartialOneTwo hcompactOneTwo))
      (poleClearedRiemannZeta_centralStrip_finiteOrder_growth_from_localBoundedness
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)
      poleClearedRiemannZeta_rightHalfPlane_finiteOrder_growth_from_EulerMaclaurin

/-- Zeta-specific ordinary finite-order growth for the pole-cleared factor in
the right critical strip, assuming the right-critical admissible-growth
package already supplied to the global finite-order wrapper. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) :=
  match poleClearedRiemannZeta_globalFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      ⟨A, B, m, hA, hB,
        fun z hz_left hz_right => hbound z⟩

/-- The reflected `0 ≤ Re s ≤ 1` half-strip and the Euler-Maclaurin
`1 ≤ Re s ≤ 2` half-strip patch to ordinary finite-order growth on the full
right critical strip. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_of_zeroOne_and_oneTwo
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (honeTwo :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hzeroOne with
  | ⟨A0, B0, m0, hA0, hB0, hbound0⟩ =>
      match honeTwo with
      | ⟨A1, B1, m1, hA1, hB1, hbound1⟩ =>
          exact
            ⟨A0 + A1, B0 + B1, m0 + m1,
              add_pos hA0 hA1, add_pos hB0 hB1,
              fun z hz_zero hz_two =>
                have hA0_nonneg : 0 ≤ A0 := le_of_lt hA0
                have hA1_nonneg : 0 ≤ A1 := le_of_lt hA1
                have hB0_nonneg : 0 ≤ B0 := le_of_lt hB0
                have hB1_nonneg : 0 ≤ B1 := le_of_lt hB1
                match le_total z.re 1 with
                | Or.inl hz_one =>
                    le_trans (hbound0 z hz_zero hz_one)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hA0_nonneg
                        (le_add_of_nonneg_right hA1_nonneg)
                        (le_add_of_nonneg_right hB1_nonneg)
                        hB0_nonneg
                        (Nat.le_add_right m0 m1))
                | Or.inr hz_one =>
                    have hm1_le : m1 ≤ m0 + m1 := by
                      exact Eq.subst
                        (motive := fun d : ℕ => m1 ≤ d)
                        (Nat.add_comm m1 m0)
                        (Nat.le_add_right m1 m0)
                    le_trans (hbound1 z hz_one hz_two)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hA1_nonneg
                        (le_add_of_nonneg_left hA0_nonneg)
                        (le_add_of_nonneg_left hB0_nonneg)
                        hB1_nonneg
                        hm1_le)⟩

end
end LFunctions
end Boundary
