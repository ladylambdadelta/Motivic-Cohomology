import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualCrossingLocations

/-!
# Principal-level collars for dual shifted correlations

Crossing collars are defined in derivative-value space.  This is canonical:
the `q`-th collar consists exactly of points where the absolute shifted
derivative lies within `eta` of `2*pi*q`.  The complement is therefore
uniformly separated from every represented principal level.  Distinct collars
are disjoint whenever twice the collar width is smaller than the spacing of
their integer levels.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualPrincipalLevel
    (q : ℕ) : ℝ :=
  2 * Real.pi * (q : ℝ)

def Complex.logarithmicPhaseDualCrossingCollar
    (t h eta L U : ℝ) (q : ℕ) : Set ℝ :=
  {x : ℝ |
    x ∈ Set.Icc L U ∧
      | |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x| -
          Complex.logarithmicPhaseDualPrincipalLevel q | ≤ eta}

def Complex.logarithmicPhaseDualCrossingCollarUnion
    (t h eta L U : ℝ) (Q : Finset ℕ) : Set ℝ :=
  ⋃ q ∈ Q,
    Complex.logarithmicPhaseDualCrossingCollar t h eta L U q

def Complex.logarithmicPhaseDualSeparatedGap
    (t h eta L U : ℝ) (Q : Finset ℕ) : Set ℝ :=
  Set.Icc L U \
    Complex.logarithmicPhaseDualCrossingCollarUnion t h eta L U Q

theorem Complex.mem_logarithmicPhaseDualCrossingCollar_iff
    (t h eta L U : ℝ) (q : ℕ) (x : ℝ) :
    x ∈ Complex.logarithmicPhaseDualCrossingCollar t h eta L U q ↔
      x ∈ Set.Icc L U ∧
        | |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x| -
            Complex.logarithmicPhaseDualPrincipalLevel q | ≤ eta := by
  exact Iff.rfl

theorem Complex.logarithmicPhaseDualCrossingCollar_subset_interval
    (t h eta L U : ℝ) (q : ℕ) :
    Complex.logarithmicPhaseDualCrossingCollar t h eta L U q ⊆
      Set.Icc L U := by
  intro x hx
  exact hx.1

theorem Complex.logarithmicPhaseDualCrossingCollarUnion_subset_interval
    (t h eta L U : ℝ) (Q : Finset ℕ) :
    Complex.logarithmicPhaseDualCrossingCollarUnion t h eta L U Q ⊆
      Set.Icc L U := by
  intro x hx
  unfold Complex.logarithmicPhaseDualCrossingCollarUnion at hx
  rcases Set.mem_iUnion.mp hx with ⟨q, hxq⟩
  rcases Set.mem_iUnion.mp hxq with ⟨hq, hxcollar⟩
  exact
    Complex.logarithmicPhaseDualCrossingCollar_subset_interval
      t h eta L U q hxcollar

theorem Complex.mem_logarithmicPhaseDualCrossingCollarUnion_iff
    (t h eta L U : ℝ) (Q : Finset ℕ) (x : ℝ) :
    x ∈ Complex.logarithmicPhaseDualCrossingCollarUnion t h eta L U Q ↔
      ∃ q ∈ Q,
        x ∈ Complex.logarithmicPhaseDualCrossingCollar t h eta L U q := by
  constructor
  · intro hx
    unfold Complex.logarithmicPhaseDualCrossingCollarUnion at hx
    rcases Set.mem_iUnion.mp hx with ⟨q, hxq⟩
    rcases Set.mem_iUnion.mp hxq with ⟨hq, hxcollar⟩
    exact Exists.intro q (And.intro hq hxcollar)
  · intro hx
    rcases hx with ⟨q, hq, hxcollar⟩
    unfold Complex.logarithmicPhaseDualCrossingCollarUnion
    exact Set.mem_iUnion.mpr
      (Exists.intro q
        (Set.mem_iUnion.mpr (Exists.intro hq hxcollar)))

theorem Complex.mem_logarithmicPhaseDualSeparatedGap_iff
    (t h eta L U : ℝ) (Q : Finset ℕ) (x : ℝ) :
    x ∈ Complex.logarithmicPhaseDualSeparatedGap t h eta L U Q ↔
      x ∈ Set.Icc L U ∧
        ∀ q ∈ Q,
          eta <
            | |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x| -
                Complex.logarithmicPhaseDualPrincipalLevel q | := by
  constructor
  · intro hx
    have hxInterval := hx.1
    have hxOutside := hx.2
    exact And.intro hxInterval
      (fun q hq =>
        lt_of_not_ge
          (fun hle =>
            hxOutside
              ((Complex.mem_logarithmicPhaseDualCrossingCollarUnion_iff
                t h eta L U Q x).mpr
                (Exists.intro q
                  (And.intro hq (And.intro hxInterval hle))))))
  · intro hx
    exact And.intro hx.1
      (fun hxUnion =>
        have hmember :=
          (Complex.mem_logarithmicPhaseDualCrossingCollarUnion_iff
            t h eta L U Q x).mp hxUnion
        match hmember with
        | ⟨q, hq, hxcollar⟩ =>
            (not_lt_of_ge hxcollar.2) (hx.2 q hq))

theorem Complex.logarithmicPhaseDual_interval_eq_collarUnion_union_gap
    (t h eta L U : ℝ) (Q : Finset ℕ) :
    Set.Icc L U =
      Complex.logarithmicPhaseDualCrossingCollarUnion t h eta L U Q ∪
        Complex.logarithmicPhaseDualSeparatedGap t h eta L U Q := by
  exact Set.Subset.antisymm
    (fun x hx =>
      match Classical.em
        (x ∈ Complex.logarithmicPhaseDualCrossingCollarUnion
          t h eta L U Q) with
      | Or.inl hcollar => Or.inl hcollar
      | Or.inr houtside => Or.inr (And.intro hx houtside))
    (fun x hx =>
      match hx with
      | Or.inl hcollar =>
          Complex.logarithmicPhaseDualCrossingCollarUnion_subset_interval
            t h eta L U Q hcollar
      | Or.inr hgap => hgap.1)

theorem Complex.logarithmicPhaseDualCrossingCollar_mono_eta
    (t h L U : ℝ) (q : ℕ) {eta₁ eta₂ : ℝ}
    (heta : eta₁ ≤ eta₂) :
    Complex.logarithmicPhaseDualCrossingCollar t h eta₁ L U q ⊆
      Complex.logarithmicPhaseDualCrossingCollar t h eta₂ L U q := by
  intro x hx
  exact And.intro hx.1 (le_trans hx.2 heta)

theorem Complex.logarithmicPhaseDualCrossingCollarUnion_mono_finset
    (t h eta L U : ℝ) {Q₁ Q₂ : Finset ℕ}
    (hQ : Q₁ ⊆ Q₂) :
    Complex.logarithmicPhaseDualCrossingCollarUnion t h eta L U Q₁ ⊆
      Complex.logarithmicPhaseDualCrossingCollarUnion t h eta L U Q₂ := by
  intro x hx
  have hmember :=
    (Complex.mem_logarithmicPhaseDualCrossingCollarUnion_iff
      t h eta L U Q₁ x).mp hx
  rcases hmember with ⟨q, hq, hxcollar⟩
  exact
    (Complex.mem_logarithmicPhaseDualCrossingCollarUnion_iff
      t h eta L U Q₂ x).mpr
      (Exists.intro q (And.intro (hQ hq) hxcollar))

theorem Real.abs_sub_le_add_abs_sub
    (x a b : ℝ) :
    |a - b| ≤ |x - a| + |x - b| := by
  have htriangle := abs_add (a - x) (x - b)
  have hsum : (a - x) + (x - b) = a - b := by
    exact sub_add_sub_cancel a x b
  have hleft : |a - x| = |x - a| := abs_sub_comm a x
  exact Eq.subst (motive := fun z : ℝ => |a - b| ≤ z + |x - b|)
    hleft.symm
    (Eq.subst (motive := fun z : ℝ => |z| ≤ |a - x| + |x - b|)
      hsum.symm htriangle)

theorem Complex.logarithmicPhaseDualCrossingCollars_disjoint_of_level_gap
    (t h eta L U : ℝ) {q r : ℕ}
    (hgap : 2 * eta <
      |Complex.logarithmicPhaseDualPrincipalLevel q -
        Complex.logarithmicPhaseDualPrincipalLevel r|) :
    Disjoint
      (Complex.logarithmicPhaseDualCrossingCollar t h eta L U q)
      (Complex.logarithmicPhaseDualCrossingCollar t h eta L U r) := by
  exact Set.disjoint_left.mpr
    (fun x hxq hxr =>
      have htriangle := Real.abs_sub_le_add_abs_sub
        |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x|
        (Complex.logarithmicPhaseDualPrincipalLevel q)
        (Complex.logarithmicPhaseDualPrincipalLevel r)
      have hsum :
          | |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x| -
              Complex.logarithmicPhaseDualPrincipalLevel q| +
            | |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x| -
              Complex.logarithmicPhaseDualPrincipalLevel r| ≤
          eta + eta :=
        add_le_add hxq.2 hxr.2
      have htwo : eta + eta = 2 * eta := (two_mul eta).symm
      have hcontra :
          |Complex.logarithmicPhaseDualPrincipalLevel q -
              Complex.logarithmicPhaseDualPrincipalLevel r| ≤ 2 * eta :=
        le_trans htriangle
          (Eq.subst (motive := fun z : ℝ => _ ≤ z) htwo.symm hsum)
      (not_le_of_gt hgap) hcontra)

theorem Complex.logarithmicPhaseDualCrossingCollar_contains_exact_location
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h eta L U : ℝ}
    (hh : 0 < h) (heta : 0 ≤ eta) {q : ℕ} (hq : 0 < q)
    (hlocation :
      Complex.logarithmicPhaseDualCrossingLocation t h q ∈ Set.Icc L U) :
    Complex.logarithmicPhaseDualCrossingLocation t h q ∈
      Complex.logarithmicPhaseDualCrossingCollar t h eta L U q := by
  have hlevel :=
    Complex.logarithmicPhaseDualCrossingLocation_derivative_abs_eq_level
      t ht hh hq
  have hzero :
      | |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h
          (Complex.logarithmicPhaseDualCrossingLocation t h q)| -
          Complex.logarithmicPhaseDualPrincipalLevel q| = 0 := by
    unfold Complex.logarithmicPhaseDualPrincipalLevel
    exact Eq.trans (congrArg abs (sub_eq_zero.mpr hlevel)) abs_zero
  exact And.intro hlocation
    (Eq.subst (motive := fun z : ℝ => z ≤ eta) hzero.symm heta)

end

end LFunctions
end Boundary
