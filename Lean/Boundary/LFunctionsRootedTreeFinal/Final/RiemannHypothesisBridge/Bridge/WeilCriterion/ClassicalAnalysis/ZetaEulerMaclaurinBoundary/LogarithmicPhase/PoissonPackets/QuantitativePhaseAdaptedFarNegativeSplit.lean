import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedFarNegativeGeometry

/-!
# Integer-distance coordinates on the far-negative tail

The far-negative ray admits an exact integer distance from the floor-defined
lower endpoint.  The first outside mode has distance one, so it already gains
one full angular frequency step; the optional head/deep decomposition below is
only a combinatorial refinement and is not required for summability.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhasePoissonFarNegativeBoundaryMode
    (t : ℝ) (a : ℤ) : ℤ :=
  Complex.logarithmicPhasePoissonModeRangeLower t a - 1

def Complex.logarithmicPhasePoissonDeepNegativeModes
    (t : ℝ) (a : ℤ) : Set ℤ :=
  {m : ℤ | m < Complex.logarithmicPhasePoissonModeRangeLower t a - 1}

theorem Complex.farNegativeBoundaryMode_lt_lower
    (t : ℝ) (a : ℤ) :
    Complex.logarithmicPhasePoissonFarNegativeBoundaryMode t a <
      Complex.logarithmicPhasePoissonModeRangeLower t a := by
  unfold Complex.logarithmicPhasePoissonFarNegativeBoundaryMode
  exact sub_one_lt _

theorem Complex.farNegativeBoundaryMode_mem_farNegative
    (t : ℝ) (a : ℤ) :
    Complex.logarithmicPhasePoissonFarNegativeBoundaryMode t a ∈
      Complex.logarithmicPhasePoissonFarNegativeModes t a := by
  exact Complex.farNegativeBoundaryMode_lt_lower t a

theorem Complex.mem_logarithmicPhasePoissonDeepNegativeModes_iff
    (t : ℝ) (a m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonDeepNegativeModes t a ↔
      m < Complex.logarithmicPhasePoissonModeRangeLower t a - 1 := by
  exact Iff.rfl

theorem Complex.deepNegative_mem_farNegative
    (t : ℝ) (a : ℤ)
    {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonDeepNegativeModes t a) :
    m ∈ Complex.logarithmicPhasePoissonFarNegativeModes t a := by
  have hdeep :
      m < Complex.logarithmicPhasePoissonModeRangeLower t a - 1 := hm
  have hboundary :
      Complex.logarithmicPhasePoissonModeRangeLower t a - 1 <
        Complex.logarithmicPhasePoissonModeRangeLower t a :=
    sub_one_lt _
  exact lt_trans hdeep hboundary

theorem Complex.farNegative_eq_boundary_union_deep
    (t : ℝ) (a : ℤ) :
    Complex.logarithmicPhasePoissonFarNegativeModes t a =
      {Complex.logarithmicPhasePoissonFarNegativeBoundaryMode t a} ∪
        Complex.logarithmicPhasePoissonDeepNegativeModes t a := by
  exact Set.ext (fun m =>
    Iff.intro
      (fun hm =>
        have hmLeBoundary :
            m ≤ Complex.logarithmicPhasePoissonModeRangeLower t a - 1 :=
          Int.le_sub_one_iff.mpr hm
        match eq_or_lt_of_le hmLeBoundary with
        | Or.inl heq => Or.inl heq
        | Or.inr hlt => Or.inr hlt)
      (fun hm =>
        match hm with
        | Or.inl heq =>
            Eq.subst
              (motive := fun value : ℤ =>
                value < Complex.logarithmicPhasePoissonModeRangeLower t a)
              heq.symm
              (Complex.farNegativeBoundaryMode_lt_lower t a)
        | Or.inr hdeep =>
            Complex.deepNegative_mem_farNegative t a hdeep))

theorem Complex.boundaryMode_not_mem_deepNegative
    (t : ℝ) (a : ℤ) :
    Complex.logarithmicPhasePoissonFarNegativeBoundaryMode t a ∉
      Complex.logarithmicPhasePoissonDeepNegativeModes t a := by
  exact fun hm =>
    (lt_irrefl (Complex.logarithmicPhasePoissonModeRangeLower t a - 1)) hm

theorem Complex.farNegativeBoundary_deep_disjoint
    (t : ℝ) (a : ℤ) :
    Disjoint
      ({Complex.logarithmicPhasePoissonFarNegativeBoundaryMode t a} : Set ℤ)
      (Complex.logarithmicPhasePoissonDeepNegativeModes t a) := by
  exact Set.disjoint_left.mpr
    (fun m hmBoundary hmDeep =>
      Complex.boundaryMode_not_mem_deepNegative t a
        (Eq.subst
          (motive := fun value : ℤ =>
            value ∈ Complex.logarithmicPhasePoissonDeepNegativeModes t a)
          hmBoundary hmDeep))

def Complex.logarithmicPhaseDeepNegativeDistance
    (t : ℝ) (a m : ℤ) : ℤ :=
  Complex.logarithmicPhasePoissonModeRangeLower t a - 1 - m

def Complex.logarithmicPhaseFarNegativeDistance
    (t : ℝ) (a m : ℤ) : ℤ :=
  Complex.logarithmicPhasePoissonModeRangeLower t a - m

theorem Complex.farNegativeDistance_pos
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    0 < Complex.logarithmicPhaseFarNegativeDistance t a m := by
  unfold Complex.logarithmicPhaseFarNegativeDistance
  exact sub_pos.mpr m.property

theorem Complex.one_le_farNegativeDistance
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    1 ≤ Complex.logarithmicPhaseFarNegativeDistance t a m := by
  exact Int.add_one_le_iff.mpr
    (Complex.farNegativeDistance_pos t a m)

theorem Complex.farNegative_mode_reconstruct
    (t : ℝ) (a m : ℤ) :
    m = Complex.logarithmicPhasePoissonModeRangeLower t a -
      Complex.logarithmicPhaseFarNegativeDistance t a m := by
  unfold Complex.logarithmicPhaseFarNegativeDistance
  exact (sub_sub_cancel
    (Complex.logarithmicPhasePoissonModeRangeLower t a) m).symm

theorem Complex.deepNegativeDistance_pos
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonDeepNegativeModes t a) :
    0 < Complex.logarithmicPhaseDeepNegativeDistance t a m := by
  unfold Complex.logarithmicPhaseDeepNegativeDistance
  exact sub_pos.mpr m.property

theorem Complex.deepNegative_mode_reconstruct
    (t : ℝ) (a m : ℤ) :
    m = Complex.logarithmicPhasePoissonModeRangeLower t a - 1 -
      Complex.logarithmicPhaseDeepNegativeDistance t a m := by
  unfold Complex.logarithmicPhaseDeepNegativeDistance
  have hfirst := sub_sub_cancel
    (Complex.logarithmicPhasePoissonModeRangeLower t a - 1) m
  exact hfirst.symm

end
end LFunctions
end Boundary
