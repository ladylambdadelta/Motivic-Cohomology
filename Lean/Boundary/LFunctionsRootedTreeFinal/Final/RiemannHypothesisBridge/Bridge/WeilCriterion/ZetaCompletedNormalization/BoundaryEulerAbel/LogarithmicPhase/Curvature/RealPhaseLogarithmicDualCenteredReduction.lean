import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualBranchIndex

/-!
# Canonical centered reduction of the dual increment

This owner separates the algebra of centered angular reduction from the
topological assertion that a surviving run does not cross a midpoint cut.
The raw dual increment is negative.  Its canonical branch index is the nearest
nonnegative angular lattice index, and addition of that fixed lattice amount
places the result in `Ioc (-pi) pi`.

The important downstream fact is deliberately stated in its strongest useful
form: on any finite interval on which the branch index is constant, raw
monotonicity transports exactly to monotonicity of the centered reduction.
No approximation or branch witness is introduced.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.centeredAngularReduction
    (v : ℝ) : ℝ :=
  v + 2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ)

def Complex.logarithmicPhaseDualContinuousReducedIncrement
    (t h x : ℝ) : ℝ :=
  Real.centeredAngularReduction
    (Complex.logarithmicPhaseDualContinuousIncrement t h x)

def Complex.logarithmicPhaseDualDiscreteReducedIncrement
    (t : ℝ) (h n : ℕ) : ℝ :=
  Real.centeredAngularReduction
    (Complex.logarithmicPhaseDualShiftedIncrement t h n)

theorem Real.centeredAngularReduction_eq
    (v : ℝ) :
    Real.centeredAngularReduction v =
      v + 2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) := by
  rfl

theorem Real.centeredAngularReduction_mem_centered_of_neg
    {v : ℝ} (hv : v < 0) :
    Real.centeredAngularReduction v ∈ Set.Ioc (-Real.pi) Real.pi := by
  unfold Real.centeredAngularReduction
  exact Real.negative_add_branch_mem_centered hv

theorem Real.centeredAngularReduction_lower_of_neg
    {v : ℝ} (hv : v < 0) :
    -Real.pi < Real.centeredAngularReduction v := by
  exact (Real.centeredAngularReduction_mem_centered_of_neg hv).1

theorem Real.centeredAngularReduction_upper_of_neg
    {v : ℝ} (hv : v < 0) :
    Real.centeredAngularReduction v ≤ Real.pi := by
  exact (Real.centeredAngularReduction_mem_centered_of_neg hv).2

theorem Real.centeredAngularReduction_eq_add_fixed
    {v : ℝ} {q : ℕ}
    (hq : Real.centeredAngularBranchIndex v = q) :
    Real.centeredAngularReduction v =
      v + 2 * Real.pi * (q : ℝ) := by
  unfold Real.centeredAngularReduction
  exact congrArg
    (fun z : ℝ => v + 2 * Real.pi * z)
    (congrArg (fun k : ℕ => (k : ℝ)) hq)

theorem Real.centeredAngularReduction_sub_eq_sub_of_branchIndex_eq
    {u v : ℝ}
    (hindex : Real.centeredAngularBranchIndex u =
      Real.centeredAngularBranchIndex v) :
    Real.centeredAngularReduction v - Real.centeredAngularReduction u =
      v - u := by
  unfold Real.centeredAngularReduction
  have hcast :
      ((Real.centeredAngularBranchIndex u : ℕ) : ℝ) =
        ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) :=
    congrArg (fun k : ℕ => (k : ℝ)) hindex
  have hscaled :
      2 * Real.pi * ((Real.centeredAngularBranchIndex u : ℕ) : ℝ) =
        2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) :=
    congrArg (fun z : ℝ => 2 * Real.pi * z) hcast
  calc
    (v + 2 * Real.pi *
          ((Real.centeredAngularBranchIndex v : ℕ) : ℝ)) -
        (u + 2 * Real.pi *
          ((Real.centeredAngularBranchIndex u : ℕ) : ℝ)) =
      (v + 2 * Real.pi *
          ((Real.centeredAngularBranchIndex v : ℕ) : ℝ)) -
        (u + 2 * Real.pi *
          ((Real.centeredAngularBranchIndex v : ℕ) : ℝ)) := by
            exact congrArg
              (fun z : ℝ =>
                (v + 2 * Real.pi *
                    ((Real.centeredAngularBranchIndex v : ℕ) : ℝ)) -
                  (u + z)) hscaled
    _ = v - u := by
      exact add_sub_add_right_eq_sub v u

theorem Real.centeredAngularReduction_le_of_le_of_branchIndex_eq
    {u v : ℝ} (huv : u ≤ v)
    (hindex : Real.centeredAngularBranchIndex u =
      Real.centeredAngularBranchIndex v) :
    Real.centeredAngularReduction u ≤
      Real.centeredAngularReduction v := by
  unfold Real.centeredAngularReduction
  have hcast :
      ((Real.centeredAngularBranchIndex u : ℕ) : ℝ) =
        ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) :=
    congrArg (fun k : ℕ => (k : ℝ)) hindex
  have hscaled :
      2 * Real.pi * ((Real.centeredAngularBranchIndex u : ℕ) : ℝ) =
        2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) :=
    congrArg (fun z : ℝ => 2 * Real.pi * z) hcast
  exact Eq.subst
    (motive := fun z : ℝ =>
      u + z ≤
        v + 2 * Real.pi *
          ((Real.centeredAngularBranchIndex v : ℕ) : ℝ))
    hscaled
    (add_le_add_right huv
      (2 * Real.pi *
        ((Real.centeredAngularBranchIndex v : ℕ) : ℝ)))

theorem Real.centeredAngularReduction_lt_of_lt_of_branchIndex_eq
    {u v : ℝ} (huv : u < v)
    (hindex : Real.centeredAngularBranchIndex u =
      Real.centeredAngularBranchIndex v) :
    Real.centeredAngularReduction u <
      Real.centeredAngularReduction v := by
  unfold Real.centeredAngularReduction
  have hcast :
      ((Real.centeredAngularBranchIndex u : ℕ) : ℝ) =
        ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) :=
    congrArg (fun k : ℕ => (k : ℝ)) hindex
  have hscaled :
      2 * Real.pi * ((Real.centeredAngularBranchIndex u : ℕ) : ℝ) =
        2 * Real.pi * ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) :=
    congrArg (fun z : ℝ => 2 * Real.pi * z) hcast
  exact Eq.subst
    (motive := fun z : ℝ =>
      u + z <
        v + 2 * Real.pi *
          ((Real.centeredAngularBranchIndex v : ℕ) : ℝ))
    hscaled
    (add_lt_add_right huv
      (2 * Real.pi *
        ((Real.centeredAngularBranchIndex v : ℕ) : ℝ)))

theorem Complex.logarithmicPhaseDualContinuousReducedIncrement_mem_centered
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h x : ℝ}
    (hh : 0 < h) (hx : 0 < x) :
    Complex.logarithmicPhaseDualContinuousReducedIncrement t h x ∈
      Set.Ioc (-Real.pi) Real.pi := by
  unfold Complex.logarithmicPhaseDualContinuousReducedIncrement
  exact Real.centeredAngularReduction_mem_centered_of_neg
    (Complex.logarithmicPhaseDualContinuousIncrement_neg t ht hh hx)

theorem Complex.logarithmicPhaseDualDiscreteReducedIncrement_mem_centered
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h n : ℕ}
    (hh : 0 < h) (hn : 0 < n) :
    Complex.logarithmicPhaseDualDiscreteReducedIncrement t h n ∈
      Set.Ioc (-Real.pi) Real.pi := by
  unfold Complex.logarithmicPhaseDualDiscreteReducedIncrement
  exact Real.centeredAngularReduction_mem_centered_of_neg
    (Complex.logarithmicPhaseDualShiftedIncrement_neg t ht hh hn)

theorem Complex.logarithmicPhaseDualContinuousReducedIncrement_nat_eq_discrete
    (t : ℝ) (h n : ℕ) :
    Complex.logarithmicPhaseDualContinuousReducedIncrement t (h : ℝ) (n : ℝ) =
      Complex.logarithmicPhaseDualDiscreteReducedIncrement t h n := by
  unfold Complex.logarithmicPhaseDualContinuousReducedIncrement
  unfold Complex.logarithmicPhaseDualDiscreteReducedIncrement
  exact congrArg Real.centeredAngularReduction
    (Complex.logarithmicPhaseDualContinuousIncrement_nat_eq t h n)

theorem Complex.logarithmicPhaseDualDiscreteReducedIncrement_eq_add_branch
    (t : ℝ) (h n : ℕ) :
    Complex.logarithmicPhaseDualDiscreteReducedIncrement t h n =
      Complex.logarithmicPhaseDualShiftedIncrement t h n +
        2 * Real.pi *
          ((Complex.logarithmicPhaseDualDiscreteBranchIndex t h n : ℕ) : ℝ) := by
  unfold Complex.logarithmicPhaseDualDiscreteReducedIncrement
  unfold Complex.logarithmicPhaseDualDiscreteBranchIndex
  exact Real.centeredAngularReduction_eq _

theorem Complex.logarithmicPhaseDualContinuousReducedIncrement_eq_add_branch
    (t h x : ℝ) :
    Complex.logarithmicPhaseDualContinuousReducedIncrement t h x =
      Complex.logarithmicPhaseDualContinuousIncrement t h x +
        2 * Real.pi *
          ((Complex.logarithmicPhaseDualContinuousBranchIndex t h x : ℕ) : ℝ) := by
  unfold Complex.logarithmicPhaseDualContinuousReducedIncrement
  unfold Complex.logarithmicPhaseDualContinuousBranchIndex
  exact Real.centeredAngularReduction_eq _

theorem Complex.logarithmicPhaseDualDiscreteReducedIncrement_le_of_raw_le
    (t : ℝ) (h n m : ℕ)
    (hraw : Complex.logarithmicPhaseDualShiftedIncrement t h n ≤
      Complex.logarithmicPhaseDualShiftedIncrement t h m)
    (hindex : Complex.logarithmicPhaseDualDiscreteBranchIndex t h n =
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h m) :
    Complex.logarithmicPhaseDualDiscreteReducedIncrement t h n ≤
      Complex.logarithmicPhaseDualDiscreteReducedIncrement t h m := by
  unfold Complex.logarithmicPhaseDualDiscreteReducedIncrement
  unfold Complex.logarithmicPhaseDualDiscreteBranchIndex at hindex
  exact Real.centeredAngularReduction_le_of_le_of_branchIndex_eq hraw hindex

theorem Complex.logarithmicPhaseDualDiscreteReducedIncrement_lt_of_raw_lt
    (t : ℝ) (h n m : ℕ)
    (hraw : Complex.logarithmicPhaseDualShiftedIncrement t h n <
      Complex.logarithmicPhaseDualShiftedIncrement t h m)
    (hindex : Complex.logarithmicPhaseDualDiscreteBranchIndex t h n =
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h m) :
    Complex.logarithmicPhaseDualDiscreteReducedIncrement t h n <
      Complex.logarithmicPhaseDualDiscreteReducedIncrement t h m := by
  unfold Complex.logarithmicPhaseDualDiscreteReducedIncrement
  unfold Complex.logarithmicPhaseDualDiscreteBranchIndex at hindex
  exact Real.centeredAngularReduction_lt_of_lt_of_branchIndex_eq hraw hindex

theorem Complex.logarithmicPhaseDualDiscreteReducedIncrement_monotone_on_Ico_of_branchIndex_const
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h a b q : ℕ} (hh : 0 < h) (ha : 0 < a)
    (hindex : ∀ n ∈ Finset.Ico a b,
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h n = q) :
    ∀ n ∈ Finset.Ico a b,
      ∀ m ∈ Finset.Ico a b,
        n ≤ m →
          Complex.logarithmicPhaseDualDiscreteReducedIncrement t h n ≤
            Complex.logarithmicPhaseDualDiscreteReducedIncrement t h m := by
  intro n hn m hm hnm
  have hraw :=
    Complex.logarithmicPhaseDualShiftedIncrement_monotone_on_Ico
      t ht hh ha n hn m hm hnm
  have hnIndex := hindex n hn
  have hmIndex := hindex m hm
  have hsame := Eq.trans hnIndex hmIndex.symm
  exact Complex.logarithmicPhaseDualDiscreteReducedIncrement_le_of_raw_le
    t h n m hraw hsame

theorem Complex.logarithmicPhaseDualDiscreteReducedIncrement_strictMono_on_Ico_of_branchIndex_const
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h a b q : ℕ} (hh : 0 < h) (ha : 0 < a)
    (hindex : ∀ n ∈ Finset.Ico a b,
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h n = q) :
    ∀ n ∈ Finset.Ico a b,
      ∀ m ∈ Finset.Ico a b,
        n < m →
          Complex.logarithmicPhaseDualDiscreteReducedIncrement t h n <
            Complex.logarithmicPhaseDualDiscreteReducedIncrement t h m := by
  intro n hn m hm hnm
  have hraw :=
    Complex.logarithmicPhaseDualShiftedIncrement_strictMono_on_Ico
      t ht hh ha n hn m hm hnm
  have hnIndex := hindex n hn
  have hmIndex := hindex m hm
  have hsame := Eq.trans hnIndex hmIndex.symm
  exact Complex.logarithmicPhaseDualDiscreteReducedIncrement_lt_of_raw_lt
    t h n m hraw hsame

theorem Complex.logarithmicPhaseDualDiscreteReducedIncrement_sub_eq_raw_sub_of_branchIndex_const
    (t : ℝ) (h a b q : ℕ)
    (hindex : ∀ n ∈ Finset.Ico a b,
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h n = q) :
    ∀ n ∈ Finset.Ico a b,
      ∀ m ∈ Finset.Ico a b,
        Complex.logarithmicPhaseDualDiscreteReducedIncrement t h m -
            Complex.logarithmicPhaseDualDiscreteReducedIncrement t h n =
          Complex.logarithmicPhaseDualShiftedIncrement t h m -
            Complex.logarithmicPhaseDualShiftedIncrement t h n := by
  intro n hn m hm
  have hnIndex := hindex n hn
  have hmIndex := hindex m hm
  have hsame := Eq.trans hnIndex hmIndex.symm
  unfold Complex.logarithmicPhaseDualDiscreteReducedIncrement
  unfold Complex.logarithmicPhaseDualDiscreteBranchIndex at hsame
  exact Real.centeredAngularReduction_sub_eq_sub_of_branchIndex_eq hsame

end

end LFunctions
end Boundary
