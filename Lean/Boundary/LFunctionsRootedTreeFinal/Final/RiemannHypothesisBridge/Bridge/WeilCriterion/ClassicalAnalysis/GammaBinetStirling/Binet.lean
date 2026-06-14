import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Basic

/-!
# Binet formula and kernel estimates

This file owns Binet's second logarithmic formula and the real majorant
estimates for its kernel.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Binet's second logarithmic formula for Gamma in the closed right
half-plane, away from the origin and after a fixed large-radius cutoff. -/
theorem Complex.Gamma_binetSecondFormula_closedRightHalfPlane :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  sorry

/-- Pointwise kernel estimate for Binet's second-formula remainder. -/
theorem Complex.binetSecondFormula_kernel_norm_le
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∀ t : ℝ,
      0 < t →
        ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
          (t / ‖w‖) /
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  sorry

/-- The Binet real majorant is integrable near zero. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioc (0 : ℝ) 1) := by
  sorry

/-- The Binet real majorant has an exponentially decaying tail. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_le_exp :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (1 : ℝ) →
          ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
            C * Real.exp (-Real.pi * t) := by
  sorry

/-- The Binet real majorant is integrable at infinity. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (1 : ℝ)) := by
  sorry

/-- The positive half-line decomposes into the local Binet interval `(0,1]`
and the tail interval `(1,∞)`. -/
theorem Real.Ioi_zero_eq_Ioc_zero_one_union_Ioi_one :
    Set.Ioi (0 : ℝ) =
      Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
  exact
    Set.ext
      (fun x =>
        ⟨fun hx =>
            Or.elim (lt_or_ge (1 : ℝ) x)
              (fun hone_lt_x => Or.inr hone_lt_x)
              (fun hx_le_one => Or.inl ⟨hx, hx_le_one⟩),
          fun hx =>
            Or.elim hx
              (fun hx_local => hx_local.1)
              (fun hx_tail => lt_trans zero_lt_one hx_tail)⟩)

/-- Joining local integrability on `(0,1]` with tail integrability on `(1,∞)`
gives integrability on `(0,∞)`. -/
theorem Real.integrableOn_Ioi_zero_of_Ioc_zero_one_and_Ioi_one
    {f : ℝ → ℝ}
    (hlocal : IntegrableOn f (Set.Ioc (0 : ℝ) 1))
    (htail : IntegrableOn f (Set.Ioi (1 : ℝ))) :
    IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  have hcover :
      Set.Ioi (0 : ℝ) =
        Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) :=
    Real.Ioi_zero_eq_Ioc_zero_one_union_Ioi_one
  have hunion :
      IntegrableOn f (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ)) :=
    integrableOn_union.mpr ⟨hlocal, htail⟩
  exact
    Eq.subst
      (motive := fun s : Set ℝ => IntegrableOn f s)
      hcover.symm
      hunion

/-- The real majorant for the Binet kernel is integrable on `(0,∞)` once its
local and tail pieces are integrable. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_from_zero_local_and_infinity
    (hlocal :
      IntegrableOn
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
        (Set.Ioc (0 : ℝ) 1))
    (htail :
      IntegrableOn
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
        (Set.Ioi (1 : ℝ))) :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (0 : ℝ)) := by
  exact
    Real.integrableOn_Ioi_zero_of_Ioc_zero_one_and_Ioi_one
      hlocal htail

/-- The Binet real majorant is integrable on the positive half-line. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (0 : ℝ)) := by
  exact
    Real.binetSecondFormula_kernel_majorant_integrableOn_from_zero_local_and_infinity
      Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one
      Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty

end

end LFunctions
end Boundary
