import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.OwnerParts.Part01_ReflectionDefinitions

/-!
# Pole-cleared zeta self-reflection transport
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Product transport for the zero-one functional equation from a multiplier
envelope and a non-circular reflected-value envelope. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_of_multiplier_and_selfReflectedEnvelope
    (hmult :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hreflected :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_product_core
      hmult hreflected

/-- High-tail zero-one strip finite-order theorem from the completed
functional equation and the noncircular self-reflected envelope.

This theorem avoids routing through the open-strip admissible-growth/PL layer:
the high-tail estimate is the direct product of the Gamma/Stirling multiplier
bound and the self-reflected zero-one strip envelope. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerEulerMaclaurinFunctionalEquationCore
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_of_multiplier_and_selfReflectedEnvelope
      (poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
        hbranch)
      (poleClearedRiemannZeta_zero_one_strip_selfReflectedVerticalTailEnvelope_ownerEulerMaclaurinFunctionalEquationCore
        boundaryLineOneAbelPartialMajorant_from_realParam
        poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
        (reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
          boundaryLineOneAbelPartialMajorant_from_realParam)
        poleClearedRightCriticalStripCompactBoundaryBound_from_compact
        hreflected)

/-- Compact-height finite-order growth on the closed zero-one strip, placed
above the noncircular owner so the owner can be assembled without referring
to the later admissible-growth/PL wrappers. -/
theorem poleClearedRiemannZeta_zero_one_strip_compactCore_growth_for_nonCircularOwner :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        ‖z.im‖ ≤ 1 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, 1, 0, hC_pos, zero_lt_one,
          fun z hz_zero hz_one hz_im =>
            have hz_two : z.re ≤ 2 :=
              le_trans hz_one poleCleared_one_le_two
            have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
              ⟨hz_zero, hz_two, hz_im⟩
            have hraw : ‖poleClearedRiemannZeta z‖ ≤ C :=
              hC_bound z hz_mem
            have hfactor_ge_one :
                (1 : ℝ) ≤ Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) := by
              have hexponent_nonneg :
                  0 ≤ (1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ) :=
                mul_nonneg zero_le_one
                  (pow_nonneg (add_nonneg zero_le_one (norm_nonneg z)) 0)
              exact le_trans
                (le_of_eq Real.exp_zero.symm)
                (Real.exp_le_exp.mpr hexponent_nonneg)
            have hC_le_target :
                C ≤ C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) := by
              exact Eq.subst
                (motive := fun value : ℝ => value ≤
                  C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)))
                (mul_one C)
                (mul_le_mul_of_nonneg_left hfactor_ge_one (le_of_lt hC_pos))
            le_trans hraw hC_le_target⟩

/-- Compact core and vertical-tail patch to ordinary finite-order growth on
the closed zero-one strip. -/
theorem poleClearedRiemannZeta_zero_one_strip_growth_of_compactCore_and_verticalTail_for_nonCircularOwner
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          ‖z.im‖ ≤ 1 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  match hcompact with
  | ⟨Ac, Bc, mc, hAc, hBc, hc⟩ =>
      match htail with
      | ⟨At, Bt, mt, hAt, hBt, ht⟩ =>
          exact
            ⟨Ac + At, Bc + Bt, mc + mt,
              add_pos hAc hAt, add_pos hBc hBt,
              fun z hz_zero hz_one =>
                have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
                have hAt_nonneg : 0 ≤ At := le_of_lt hAt
                have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
                have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
                match le_total ‖z.im‖ 1 with
                | Or.inl hcompact_im =>
                    le_trans (hc z hz_zero hz_one hcompact_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAc_nonneg
                        (le_add_of_nonneg_right hAt_nonneg)
                        (le_add_of_nonneg_right hBt_nonneg)
                        hBc_nonneg
                        (Nat.le_add_right mc mt))
                | Or.inr htail_im =>
                    have hdegree : mt ≤ mc + mt := by
                      exact Eq.subst
                        (motive := fun d : ℕ => mt ≤ d)
                        (Nat.add_comm mt mc)
                        (Nat.le_add_right mt mc)
                    le_trans (ht z hz_zero hz_one htail_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAt_nonneg
                        (le_add_of_nonneg_left hAc_nonneg)
                        (le_add_of_nonneg_left hBc_nonneg)
                        hBt_nonneg
                        hdegree)⟩

/-- Independent zero-one strip finite-order theorem used only to reflect the
right-hand value in the completed functional equation.

The unresolved analytic content is isolated in the high-tail
Euler-Maclaurin/functional-equation theorem above; this wrapper only patches
that tail estimate with the compact-height local boundedness core. -/
theorem poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_ownerEulerMaclaurinFunctionalEquationCore
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact
    poleClearedRiemannZeta_zero_one_strip_growth_of_compactCore_and_verticalTail_for_nonCircularOwner
      poleClearedRiemannZeta_zero_one_strip_compactCore_growth_for_nonCircularOwner
      (poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerEulerMaclaurinFunctionalEquationCore
        hbranch hreflected)

/-- Noncircular interior admissible growth on the zero-one strip.

This is a consequence of the noncircular ordinary finite-order theorem above:
polynomial-exponential finite order is stronger than the subcritical
double-exponential admissible envelope required by the strip
Phragmen-Lindelöf interface. -/
theorem poleClearedRiemannZeta_zero_one_strip_admissible_growth_ownerEulerMaclaurinFunctionalEquationCore
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    ∃ c : ℝ,
      c < Real.pi / (1 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 0 1)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 0 1 zero_lt_one
      (poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_ownerEulerMaclaurinFunctionalEquationCore
        hbranch hreflected)

/-- Compatibility exposure of the non-circular reflected-value envelope on the
self-reflected zero-one strip.

The genuine analytic input is the `hreflected` hypothesis.  This theorem keeps
the functional-equation owner API stable without pretending to construct that
reflected envelope from the later zero-one strip growth conclusion. -/
theorem poleClearedRiemannZeta_zero_one_strip_selfReflectedVerticalTailEnvelope_ownerFunctionalEquationNoncircular
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
      hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary := by
  exact
    poleClearedRiemannZeta_zero_one_strip_selfReflectedVerticalTailEnvelope_ownerEulerMaclaurinFunctionalEquationCore
      hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected

/-- Owner transport theorem: noncircular vertical-tail finite-order growth on
`0 ≤ Re s ≤ 1` from the completed functional equation, Gamma/Stirling
multiplier control, and the independently supplied reflected-value envelope. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationNoncircularCore
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    PoleClearedZeroOneStripFunctionalEquationVerticalTailGrowth
      hbranch hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_of_multiplier_and_selfReflectedEnvelope
      (poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
        hbranch)
      (poleClearedRiemannZeta_zero_one_strip_selfReflectedVerticalTailEnvelope_ownerFunctionalEquationNoncircular
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected)

/-- Noncircular ordinary finite-order owner on the closed zero-one strip.

This is now the compact-core/vertical-tail assembly theorem.  The remaining
analytic work is the noncircular vertical-tail functional-equation leaf above;
this theorem no longer consumes admissible-growth or PL consequences. -/
theorem poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_ownerFunctionalEquationNoncircular
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact
    poleClearedRiemannZeta_zero_one_strip_growth_of_compactCore_and_verticalTail_for_nonCircularOwner
      poleClearedRiemannZeta_zero_one_strip_compactCore_growth_for_nonCircularOwner
      (poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationNoncircularCore
        hbranch hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected)

/-- Noncircular admissible-growth envelope on the genuine open zero-one strip.

This is now only the generic finite-order-to-admissible transport from the
noncircular closed-strip functional-equation owner above. -/
theorem poleClearedRiemannZeta_zero_one_strip_admissible_growth_ownerFunctionalEquationNoncircular
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    ∃ c : ℝ,
      c < Real.pi / (1 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 0 1)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 0 1 zero_lt_one
      (poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_ownerFunctionalEquationNoncircular
        hbranch hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected)

/-- Strip-PL vertical-tail consequence on the reflected zero-one strip.

This is retained as a compatibility consequence of the admissible-growth
envelope and the two vertical boundary estimates.  It is not the noncircular
owner used to prove the finite-order input. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_from_boundary_and_PL_nonCircular
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_finite_order_growth_of_boundary_envelopes_by_damping
    poleClearedRiemannZeta 0 1 zero_lt_one
    poleClearedRiemannZeta_zero_one_strip_diffContOnCl
    (poleClearedRiemannZeta_zero_one_strip_admissible_growth_ownerFunctionalEquationNoncircular
      hbranch hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected)
    (match poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound
        hbranch with
    | ⟨A, B, m, hA, hB, hleft⟩ =>
        ⟨A, B, m, hA, hB,
          fun z hz_re hz_im =>
            hleft z hz_re hz_im (hpartialLeft z hz_re hz_im)⟩)
    (match poleClearedRiemannZeta_boundaryLine_one_growth_bound_standard with
    | ⟨A, B, m, hA, hB, hright⟩ =>
        ⟨A, B, m, hA, hB,
          fun z hz_re hz_im =>
            hright z hz_re hz_im (hpartialOneTwo z hz_re hz_im)⟩)

/-- Compact-height finite-order growth for the removable pole-cleared zeta on
the closed half-strip `0 ≤ Re s ≤ 1`. -/
theorem poleClearedRiemannZeta_zero_one_strip_compactCore_growth_from_localBoundedness :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        ‖z.im‖ ≤ 1 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, 1, 0, hC_pos, zero_lt_one,
          fun z hz_zero hz_one hz_im =>
            have hz_two : z.re ≤ 2 :=
              le_trans hz_one poleCleared_one_le_two
            have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
              ⟨hz_zero, hz_two, hz_im⟩
            have hraw : ‖poleClearedRiemannZeta z‖ ≤ C :=
              hC_bound z hz_mem
            have hfactor_ge_one :
                (1 : ℝ) ≤ Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) := by
              have hexponent_nonneg :
                  0 ≤ (1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ) :=
                mul_nonneg zero_le_one
                  (pow_nonneg (add_nonneg zero_le_one (norm_nonneg z)) 0)
              exact le_trans
                (le_of_eq Real.exp_zero.symm)
                (Real.exp_le_exp.mpr hexponent_nonneg)
            have hC_le_target :
                C ≤ C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) := by
              exact Eq.subst
                (motive := fun value : ℝ => value ≤
                  C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)))
                (mul_one C)
                (mul_le_mul_of_nonneg_left hfactor_ge_one (le_of_lt hC_pos))
            le_trans hraw hC_le_target⟩

/-- Compact core and PL vertical tail patch to finite-order growth on the
whole bounded strip `0 ≤ Re s ≤ 1`. -/
theorem poleClearedRiemannZeta_zero_one_strip_growth_of_compactCore_and_verticalTail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          ‖z.im‖ ≤ 1 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  match hcompact with
  | ⟨Ac, Bc, mc, hAc, hBc, hc⟩ =>
      match htail with
      | ⟨At, Bt, mt, hAt, hBt, ht⟩ =>
          exact
            ⟨Ac + At, Bc + Bt, mc + mt,
              add_pos hAc hAt, add_pos hBc hBt,
              fun z hz_zero hz_one =>
                have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
                have hAt_nonneg : 0 ≤ At := le_of_lt hAt
                have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
                have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
                match le_total ‖z.im‖ 1 with
                | Or.inl hcompact_im =>
                    le_trans (hc z hz_zero hz_one hcompact_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAc_nonneg
                        (le_add_of_nonneg_right hAt_nonneg)
                        (le_add_of_nonneg_right hBt_nonneg)
                        hBc_nonneg
                        (Nat.le_add_right mc mt))
                | Or.inr htail_im =>
                    have hdegree : mt ≤ mc + mt := by
                      exact Eq.subst
                        (motive := fun d : ℕ => mt ≤ d)
                        (Nat.add_comm mt mc)
                        (Nat.le_add_right mt mc)
                    le_trans (ht z hz_zero hz_one htail_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAt_nonneg
                        (le_add_of_nonneg_left hAc_nonneg)
                        (le_add_of_nonneg_left hBc_nonneg)
                        hBt_nonneg
                        hdegree)⟩

/-- Noncircular vertical-tail finite-order growth on the reflected zero-one
strip.

This compatibility theorem delegates to the direct functional-equation
vertical-tail owner, not to the admissible-growth/PL route. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationNoncircular
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationNoncircularCore
      hbranch hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected

/-- Noncircular ordinary finite-order growth on the closed half-strip
`0 ≤ Re s ≤ 1`.

This compatibility name now points directly to the closed-strip
functional-equation owner, avoiding the admissible-growth/PL/tail cycle. -/
theorem poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_nonCircular
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact
    poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_ownerFunctionalEquationNoncircular
      hbranch hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected

/-- Ordinary finite-order growth on the closed half-strip `0 ≤ Re s ≤ 1`.

This is the exact reflected-side owner theorem needed before the `0..1` and
`1..2` half-strip estimates can be patched into the full right-critical
ordinary finite-order envelope.  The functional equation by itself does not
transport this strip to the established Euler-Maclaurin `1 ≤ Re s ≤ 2` strip:
if `0 ≤ Re s ≤ 1`, then `0 ≤ Re (1 - s) ≤ 1`.  The remaining analytic content is
therefore the completed-functional-equation strip transport with Gamma/Stirling
control and a noncircular finite-order strip estimate on this reflected band. -/
theorem poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact
    poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_from_functionalEquation
      hbranch hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary

end
end LFunctions
end Boundary
