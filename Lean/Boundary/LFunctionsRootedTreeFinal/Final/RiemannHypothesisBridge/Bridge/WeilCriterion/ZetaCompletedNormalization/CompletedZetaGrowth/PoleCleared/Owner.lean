import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FunctionalEquationTransport.Owner

/-!
# Pole-cleared zeta growth

This owner layer contains finite-order estimates for the pole-cleared zeta factor.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Helper: Numeric fact for growth bounds. -/
private lemma zero_le_two_real : (0 : ℝ) ≤ 2 :=
  zero_le_two

/-- Helper: Numeric fact for growth bounds. -/
private lemma zero_lt_one_real : (0 : ℝ) < 1 :=
  zero_lt_one

/-- Helper: Algebraic identity for polynomial coefficient. -/
private lemma poly_coeff_identity (P : ℝ) : 3 * P + 3 = 3 * (P + 1) := by
  calc
    3 * P + 3 = 3 * P + 3 * 1 := by
      exact congrArg (fun x : ℝ => 3 * P + x) (mul_one 3).symm
    _ = 3 * (P + 1) := by
      exact (mul_add 3 P 1).symm

/-- Helper: Algebraic regrouping for the completed-zeta pole bound. -/
private lemma pole_bound_coeff_regroup (P : ℝ) :
    (P + 2) + (2 * P + 1) = 3 * P + 3 := by
  calc
    (P + 2) + (2 * P + 1) =
        (P + 2 * P) + (2 + 1) := by
      exact add_add_add_comm P 2 (2 * P) 1
    _ = (P + 2 * P) + 3 := by
      exact congrArg (fun x : ℝ => (P + 2 * P) + x) (two_add_one_eq_three)
    _ = ((1 : ℝ) * P + 2 * P) + 3 := by
      exact congrArg (fun x : ℝ => (x + 2 * P) + 3) (one_mul P).symm
    _ = ((1 : ℝ) + 2) * P + 3 := by
      exact congrArg (fun x : ℝ => x + 3) (add_mul 1 2 P).symm
    _ = 3 * P + 3 := by
      exact congrArg (fun x : ℝ => x * P + 3) (one_add_two_eq_three)

/-- Helper: Arithmetic normalization for the far-right pole face. -/
private lemma one_add_neg_two_eq_neg_one : (1 : ℝ) + (-2) = -1 := by
  calc
    (1 : ℝ) + (-2) = 1 + (-(1 + 1)) := by
      rfl
    _ = 1 + ((-1) + (-1)) := by
      exact congrArg (fun x : ℝ => 1 + x) (neg_add 1 1)
    _ = (1 + (-1)) + (-1) := by
      exact (add_assoc 1 (-1) (-1)).symm
    _ = 0 + (-1) := by
      exact congrArg (fun x : ℝ => x + (-1)) (add_neg_cancel 1)
    _ = -1 := by
      exact zero_add (-1)

/-- Helper: Integer inequality for sum. -/
private lemma int_sum_ineq (n : ℕ) : (1 : ℤ) - (n : ℤ) - 1 = -(n : ℤ) := by
  calc
    (1 : ℤ) - (n : ℤ) - 1 =
        1 + (-(n : ℤ)) + (-1) := by
      exact congrArg (fun x : ℤ => x + (-1)) (sub_eq_add_neg 1 (n : ℤ))
    _ = 1 + (-1) + (-(n : ℤ)) := by
      exact add_right_comm 1 (-(n : ℤ)) (-1)
    _ = 0 - (n : ℤ) := by
      exact congrArg (fun x : ℤ => x + (-(n : ℤ))) (add_neg_cancel 1)
    _ = -(n : ℤ) := Int.zero_sub (n : ℤ)

/-- Helper: One is at most two. -/
private lemma one_le_two : (1 : ℝ) ≤ 2 :=
  calc
    (1 : ℝ) ≤ 1 + 1 := le_add_of_nonneg_right zero_le_one
    _ = 2 := one_add_one_eq_two

/-- Global reflected Abel partial-sum majorant needed on the left edge `re = 0`. -/
def ReflectedBoundaryAbelPartialMajorant : Prop :=
  ∀ z : ℂ,
    z.re = 0 →
    1 ≤ ‖z.im‖ →
    ∀ {x : ℝ},
      (⌊2 + ‖((1 : ℂ) - z).im‖⌋₊ : ℝ) ≤ x →
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum
            ((1 : ℂ) - z).im ⌊x⌋₊‖ ≤
          8 * ((x / ‖((1 : ℂ) - z).im‖) +
              Real.sqrt (1 + ‖((1 : ℂ) - z).im‖)) *
            Real.log (2 + x)

/-- Uniform bounded-boundary vertical-tail input for the right critical strip. -/
def PoleClearedRightCriticalStripBoundedTailBoundary : Prop :=
  ∃ A : ℝ,
    0 < A ∧
    (∀ z : ℂ,
      z.re = 0 →
      1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤ A) ∧
    (∀ z : ℂ,
      z.re = 2 →
      1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤ A)

/-- Uniform bounded-boundary compact-height input for the right critical strip. -/
def PoleClearedRightCriticalStripCompactBoundaryBound : Prop :=
  ∃ C : ℝ,
    0 < C ∧
    (∀ z : ℂ,
      z.re = 0 →
      ¬ 1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤ C) ∧
    (∀ z : ℂ,
      z.re = 2 →
      ¬ 1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤ C)

theorem poleClearedRiemannZeta_centralStrip_compactCore_finiteOrder_growth :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖z.im‖ ≤ 1 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, 1, 0, hC_pos, zero_lt_one,
          fun z hz0 hz2 hzim =>
            have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
              ⟨hz0, hz2, hzim⟩
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
              calc
                C = C * 1 := by
                  exact (mul_one C).symm
                _ ≤ C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) :=
                  mul_le_mul_of_nonneg_left hfactor_ge_one (le_of_lt hC_pos)
            le_trans hraw hC_le_target⟩

/-- Vertical-tail finite-order growth in the central strip for the pole-cleared zeta factor.

This is the unbounded-height part of the central strip.  Its proof belongs to
the standard zeta strip-growth theorem: combine the left boundary obtained from
the completed functional equation and Gamma/Stirling owner estimates with the
right boundary obtained from the Dirichlet-series/Euler-Maclaurin side, then use
the generic strip finite-order/Phragmen-Lindelöf API. -/
theorem poleClearedRiemannZeta_centralStrip_verticalTail_growth_from_PL_transport
    (hhol :
      DiffContOnCl ℂ poleClearedRiemannZeta
        (Complex.re ⁻¹' Set.Ioo 0 2))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (2 - 0) ∧
        ∃ D : ℝ,
          poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        (∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ A) ∧
        (∀ z : ℂ,
          z.re = 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ A))
    (hcompactBoundary :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = 0 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = 2 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 0 2 zero_lt_two hhol hfinite hleft hright
    htail hcompactBoundary

/-- The exact PL input package for the central-strip vertical tail.

The left edge is the completed-functional-equation/Gamma-Stirling estimate; the
right edge is the Dirichlet-series/Euler-Maclaurin estimate; the interior
admissible growth is the finite-order zeta input already isolated above. -/
theorem poleClearedRiemannZeta_centralStrip_verticalTail_PL_input_package
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft :
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ∀ {x : ℝ},
          (⌊2 + ‖((1 : ℂ) - z).im‖⌋₊ : ℝ) ≤ x →
            ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum
                ((1 : ℂ) - z).im ⌊x⌋₊‖ ≤
              8 * ((x / ‖((1 : ℂ) - z).im‖) +
                  Real.sqrt (1 + ‖((1 : ℂ) - z).im‖)) *
                Real.log (2 + x))
    (htail : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    DiffContOnCl ℂ poleClearedRiemannZeta
        (Complex.re ⁻¹' Set.Ioo 0 2) ∧
      (∃ c : ℝ,
        c < Real.pi / (2 - 0) ∧
        ∃ D : ℝ,
          poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) ∧
      (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
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
    ⟨poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl,
      poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth
        hpartialOneTwo htailOneTwo hcompactOneTwo hpartialLeft htail hcompactBoundary,
      match poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound
          hbranch with
      | ⟨A, B, m, hA, hB, hleft⟩ =>
          ⟨A, B, m, hA, hB,
            fun z hz_re hz_im =>
              hleft z hz_re hz_im (hpartialLeft z hz_re hz_im)⟩,
      poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_dirichletSeries_growth_bound⟩

theorem poleClearedRiemannZeta_centralStrip_verticalTail_finiteOrder_growth_from_boundary_inputs
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft :
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ∀ {x : ℝ},
          (⌊2 + ‖((1 : ℂ) - z).im‖⌋₊ : ℝ) ≤ x →
            ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum
                ((1 : ℂ) - z).im ⌊x⌋₊‖ ≤
              8 * ((x / ‖((1 : ℂ) - z).im‖) +
                  Real.sqrt (1 + ‖((1 : ℂ) - z).im‖)) *
                Real.log (2 + x))
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        (∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ A) ∧
        (∀ z : ℂ,
          z.re = 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ A))
    (hcompactBoundary :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = 0 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = 2 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) :=
  match poleClearedRiemannZeta_centralStrip_verticalTail_PL_input_package
      hbranch hpartialOneTwo htailOneTwo hcompactOneTwo hpartialLeft htail hcompactBoundary with
  | ⟨hhol, hfinite, hleft, hright⟩ =>
      poleClearedRiemannZeta_centralStrip_verticalTail_growth_from_PL_transport
        hhol hfinite hleft hright htail hcompactBoundary

/-- Compact core and vertical tails patch to finite-order growth on the whole
central strip. -/
theorem poleClearedRiemannZeta_centralStrip_finiteOrder_growth_of_compactCore_and_verticalTail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖z.im‖ ≤ 1 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
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
  match hcompact with
  | ⟨Ac, Bc, mc, hAc, hBc, hc⟩ =>
      match htail with
      | ⟨At, Bt, mt, hAt, hBt, ht⟩ =>
          exact
            ⟨Ac + At, Bc + Bt, mc + mt,
              add_pos hAc hAt, add_pos hBc hBt,
              fun z hz0 hz2 =>
                have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
                have hAt_nonneg : 0 ≤ At := le_of_lt hAt
                have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
                have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
                match le_total ‖z.im‖ 1 with
                | Or.inl hcompact_im =>
                    le_trans (hc z hz0 hz2 hcompact_im)
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
                    le_trans (ht z hz0 hz2 htail_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAt_nonneg
                        (le_add_of_nonneg_left hAc_nonneg)
                        (le_add_of_nonneg_left hBc_nonneg)
                        hBt_nonneg
                        hdegree)⟩

/-- Central compact-strip finite-order growth for the pole-cleared zeta factor.

This is the local boundedness part of the global finite-order theorem.  The
removable value at `1` is already built into `poleClearedRiemannZeta`; on the
closed strip `0 ≤ Re z ≤ 2`, compact/local boundedness gives an ordinary
finite-order envelope with fixed constants; cf. Boas, Ch. 1. -/
theorem poleClearedRiemannZeta_centralStrip_finiteOrder_growth_from_localBoundedness
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft :
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ∀ {x : ℝ},
          (⌊2 + ‖((1 : ℂ) - z).im‖⌋₊ : ℝ) ≤ x →
            ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum
                ((1 : ℂ) - z).im ⌊x⌋₊‖ ≤
              8 * ((x / ‖((1 : ℂ) - z).im‖) +
                  Real.sqrt (1 + ‖((1 : ℂ) - z).im‖)) *
                Real.log (2 + x))
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        (∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ A) ∧
        (∀ z : ℂ,
          z.re = 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ A))
    (hcompactBoundary :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = 0 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = 2 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_centralStrip_finiteOrder_growth_of_compactCore_and_verticalTail
      poleClearedRiemannZeta_centralStrip_compactCore_finiteOrder_growth
      (poleClearedRiemannZeta_centralStrip_verticalTail_finiteOrder_growth_from_boundary_inputs
        hbranch hpartialOneTwo htailOneTwo hcompactOneTwo hpartialLeft htail hcompactBoundary)

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
  | ⟨Al, Bl, ml, hAl, hBl, hleft_bound⟩ =>
      match hcentral with
      | ⟨Ac, Bc, mc, hAc, hBc, hcentral_bound⟩ =>
          match hright with
          | ⟨Ar, Br, mr, hAr, hBr, hright_bound⟩ =>
              let A : ℝ := Al + Ac + Ar
              let B : ℝ := Bl + Bc + Br
              let m : ℕ := ml + mc + mr
              have hAl_nonneg : 0 ≤ Al := le_of_lt hAl
              have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
              have hAr_nonneg : 0 ≤ Ar := le_of_lt hAr
              have hBl_nonneg : 0 ≤ Bl := le_of_lt hBl
              have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
              have hBr_nonneg : 0 ≤ Br := le_of_lt hBr
              have hA_pos : 0 < A :=
                add_pos (add_pos hAl hAc) hAr
              have hB_pos : 0 < B :=
                add_pos (add_pos hBl hBc) hBr
              exact
                ⟨A, B, m, hA_pos, hB_pos,
                  fun z =>
                    have hB_l_le : Bl ≤ B :=
                      le_trans (le_add_of_nonneg_right hBc_nonneg)
                        (le_add_of_nonneg_right hBr_nonneg)
                    have hB_c_le : Bc ≤ B := by
                      have hBc_le_Bl_Bc : Bc ≤ Bl + Bc :=
                        le_add_of_nonneg_left hBl_nonneg
                      exact le_trans hBc_le_Bl_Bc
                        (le_add_of_nonneg_right hBr_nonneg)
                    have hB_r_le : Br ≤ B := by
                      have hBr_le_Bc_Br : Br ≤ Bc + Br :=
                        le_add_of_nonneg_left hBc_nonneg
                      have hBc_Br_le_B : Bc + Br ≤ B := by
                        calc
                          Bc + Br ≤ Al + (Bc + Br) :=
                            le_add_of_nonneg_left hAl_nonneg
                          _ = B := by
                            exact (add_assoc Al Bc Br).symm
                      exact le_trans hBr_le_Bc_Br hBc_Br_le_B
                    match le_total z.re 0 with
                    | Or.inl hz_left =>
                        have hraw :
                            ‖poleClearedRiemannZeta z‖ ≤
                              Al * Real.exp (Bl * (1 + ‖z‖) ^ ml) :=
                          hleft_bound z hz_left
                        have hA_l_le : Al ≤ A :=
                          le_trans (le_add_of_nonneg_right hAc_nonneg)
                            (le_add_of_nonneg_right hAr_nonneg)
                        le_trans hraw
                          (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                            hAl_nonneg hA_l_le hB_l_le hBl_nonneg
                            (Nat.le_add_right ml (mc + mr)))
                    | Or.inr hz_nonneg =>
                        match le_total 2 z.re with
                        | Or.inl hz_right =>
                            have hraw :
                                ‖poleClearedRiemannZeta z‖ ≤
                                  Ar * Real.exp (Br * (1 + ‖z‖) ^ mr) :=
                              hright_bound z hz_right
                            have hA_r_le : Ar ≤ A := by
                              have hAr_le_Ac_Ar : Ar ≤ Ac + Ar :=
                                le_add_of_nonneg_left hAc_nonneg
                              have hAc_Ar_le_A : Ac + Ar ≤ A := by
                                calc
                                  Ac + Ar ≤ Al + (Ac + Ar) :=
                                    le_add_of_nonneg_left hAl_nonneg
                                  _ = A := by
                                    exact (add_assoc Al Ac Ar).symm
                              exact le_trans hAr_le_Ac_Ar hAc_Ar_le_A
                            have hm_r_le : mr ≤ m := by
                              have hmc_mr_le : mr ≤ mc + mr :=
                                Nat.le_add_left mr mc
                              have htarget : mc + mr ≤ m := by
                                exact Nat.le_add_left (mc + mr) ml
                              exact le_trans hmc_mr_le htarget
                            le_trans hraw
                              (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                                hAr_nonneg hA_r_le hB_r_le hBr_nonneg hm_r_le)
                        | Or.inr hz_le_two =>
                            have hraw :
                                ‖poleClearedRiemannZeta z‖ ≤
                                  Ac * Real.exp (Bc * (1 + ‖z‖) ^ mc) :=
                              hcentral_bound z hz_nonneg hz_le_two
                            have hA_c_le : Ac ≤ A := by
                              have hAc_le_Al_Ac : Ac ≤ Al + Ac :=
                                le_add_of_nonneg_left hAl_nonneg
                              exact le_trans hAc_le_Al_Ac
                                (le_add_of_nonneg_right hAr_nonneg)
                            have hm_c_le : mc ≤ m := by
                              have hmc_le_ml_mc : mc ≤ ml + mc :=
                                Nat.le_add_left mc ml
                              have htarget : ml + mc ≤ m :=
                                Nat.le_add_right (ml + mc) mr
                              exact le_trans hmc_le_ml_mc htarget
                            le_trans hraw
                              (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                                hAc_nonneg hA_c_le hB_c_le hBc_nonneg hm_c_le)⟩

theorem poleClearedRiemannZeta_globalFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htail : PoleClearedRightCriticalStripBoundedTailBoundary)
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
        hbranch hpartialOneTwo htailOneTwo hcompactOneTwo)
      (poleClearedRiemannZeta_centralStrip_finiteOrder_growth_from_localBoundedness
        hbranch hpartialOneTwo htailOneTwo hcompactOneTwo hpartialLeft htail hcompactBoundary)
      poleClearedRiemannZeta_rightHalfPlane_finiteOrder_growth_from_EulerMaclaurin

/-- Zeta-specific ordinary finite-order growth for the pole-cleared factor in
the right critical strip.

This is only the restriction of the global finite-order theorem for
`(s - 1)ζ(s)` to the closed right critical strip. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htail : PoleClearedRightCriticalStripBoundedTailBoundary)
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
      hbranch hpartialOneTwo htailOneTwo hcompactOneTwo hpartialLeft htail hcompactBoundary with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      ⟨A, B, m, hA, hB, fun z _hz_left _hz_right => hbound z⟩

/-- Standard finite-order theorem for the pole-cleared Riemann zeta factor in the right
critical strip.

This is the exact zeta finite-order theorem needed by the strip damping argument.  Its
analytic proof is the standard meromorphic finite-order estimate for `ζ`, with the pole at
`1` removed by `poleClearedRiemannZeta`: Abel/Euler-Maclaurin gives the right boundary,
the completed functional equation plus the Gamma-ratio Stirling estimates gives the left
boundary, local boundedness handles the removable pole, and the finite-order strip
normalization converts those inputs to the sub-critical double-exponential envelope. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htail : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 0 2 zero_lt_two
      (poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin
        hpartialOneTwo htailOneTwo hcompactOneTwo hpartialLeft htail hcompactBoundary)

/-- Standard zeta finite-order input for the pole-cleared factor inside the right
critical strip.

This is only name transport from the exact standard finite-order theorem for the
pole-cleared Riemann zeta factor. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_standardZetaInput
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htail : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth
    hpartialOneTwo htailOneTwo hcompactOneTwo hpartialLeft htail hcompactBoundary

/-- Deep zeta-growth owner primitive for the pole-cleared factor inside the right
critical strip.

The analytic content is isolated in
`poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth`;
this owner primitive is only the public name consumed by the strip
Phragmen-Lindelöf layer. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_ownerPrimitive
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htail : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_standardZetaInput
    hpartialOneTwo htailOneTwo hcompactOneTwo hpartialLeft htail hcompactBoundary

/-- Interior admissible finite-order envelope for the pole-cleared zeta factor in the
right critical strip.

This is the damping-side zeta-growth root consumed by the generic strip
Phragmen-Lindelöf theorem.  It is a thin wrapper over the standard finite-order theorem
for the pole-cleared Riemann zeta factor in this bounded-width strip. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htail : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_ownerPrimitive
    hpartialOneTwo htailOneTwo hcompactOneTwo hpartialLeft htail hcompactBoundary

/-- Vertical-tail strip estimate for the removable pole-cleared zeta factor.

This is the zeta-side consumer of the generic strip Phragmen-Lindelöf theorem before
transporting away from the pole face to `(s - 1) ζ(s)`. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound_of_strip_inputs
    (hhol :
      DiffContOnCl ℂ poleClearedRiemannZeta
        (Complex.re ⁻¹' Set.Ioo 0 2))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (2 - 0) ∧
        ∃ D : ℝ,
          poleClearedRiemannZeta =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 0 2 zero_lt_two hhol hfinite hleft hright
    htail hcompactBoundary

/-- Vertical-tail strip estimate for the removable pole-cleared zeta factor.

This theorem is now reduced to the immediate strip inputs for the pole-cleared
normalization: strip holomorphy, admissible strip growth, and the two vertical-edge
finite-order estimates. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htail : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) :=
  match poleClearedRiemannZeta_rightCriticalStrip_verticalBoundary_growth_bound hbranch with
  | ⟨hleft, hright⟩ =>
      poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound_of_strip_inputs
        poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl
        (poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth
          hpartialOneTwo htailOneTwo hcompactOneTwo hpartialLeft htail hcompactBoundary)
        (match hleft with
        | ⟨A, B, m, hA, hB, hleftBound⟩ =>
            ⟨A, B, m, hA, hB,
              fun z hz_re hz_im =>
                hleftBound z hz_re hz_im (hpartialLeft z hz_re hz_im)⟩)
        hright
        htail
        hcompactBoundary

/-- Vertical-tail pole-cleared zeta strip estimate.

This is the final zeta-specific consumer of the generic strip Phragmen-Lindelöf
pillar `strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order`.
The remaining zeta inputs are exactly the classical ones: holomorphicity after pole
clearing, right-boundary growth from the Dirichlet-series estimate, and left-boundary
growth from the functional equation/completed normalization with Gamma control. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htail : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound
      hbranch hpartialOneTwo htailOneTwo hcompactOneTwo hpartialLeft htail hcompactBoundary with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      exact
        ⟨A, B, m, hA, hB,
          fun z hz0 hz2 hzim =>
            have hz_ne_one : z ≠ 1 := fun hz_eq =>
              have him_zero : z.im = 0 := by
                calc
                  z.im = (1 : ℂ).im := by
                    exact congrArg Complex.im hz_eq
                  _ = 0 := by
                    rfl
              have hnorm_im_zero : ‖z.im‖ = 0 := by
                exact (congrArg norm him_zero).trans norm_zero
              have hle_zero : (1 : ℝ) ≤ 0 :=
                hzim.trans_eq hnorm_im_zero
              (not_le_of_gt zero_lt_one) hle_zero
            have hpc :
                poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
              poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
            Eq.subst
              (motive := fun w : ℂ =>
                ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
              hpc
              (hbound z hz0 hz2 hzim)⟩

/-- Compact and vertical-tail estimates combine to the right-critical-strip pole-cleared
zeta bound. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound_of_compact_and_tail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖z.im‖ ≤ 1 →
          ‖(z - 1) * riemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖(z - 1) * riemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hcompact with
  | ⟨Ac, Bc, mc, hAc, hBc, hc⟩ =>
      match htail with
      | ⟨At, Bt, mt, hAt, hBt, ht⟩ =>
          exact
            ⟨Ac + At, Bc + Bt, mc + mt,
              add_pos hAc hAt, add_pos hBc hBt,
              fun z hz0 hz2 =>
                have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
                have hAt_nonneg : 0 ≤ At := le_of_lt hAt
                have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
                have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
                match le_total ‖z.im‖ 1 with
                | Or.inl hcompact_im =>
                    le_trans (hc z hz0 hz2 hcompact_im)
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
                    le_trans (ht z hz0 hz2 htail_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAt_nonneg
                        (le_add_of_nonneg_left hAc_nonneg)
                        (le_add_of_nonneg_left hBc_nonneg)
                        hBt_nonneg
                        hdegree)⟩

/-- Pole-cleared finite-order growth for `ζ` in the bounded-width right critical strip. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htailBoundary : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound_of_compact_and_tail
    riemannZeta_rightCriticalStrip_poleCleared_compact_growth_bound
    (riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound
      hbranch hpartialOneTwo htailOneTwo hcompactOneTwo hpartialLeft htailBoundary hcompactBoundary)

end
end LFunctions
end Boundary
