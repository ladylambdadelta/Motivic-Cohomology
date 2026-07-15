import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.ScalarNormalization

/-!
# Unit-block realization of the periodic centered primitive
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A natural-number translate represents zero in the unit additive circle. -/
theorem unitAddCircle_natCast_eq_zero (k : ℕ) :
    (((k : ℕ) : ℝ) : UnitAddCircle) = 0 := by
  have hwitness : (k : ℤ) • (1 : ℝ) = (k : ℝ) := by
    exact Eq.trans
      (zsmul_one (R := ℝ) (k : ℤ))
      (Int.cast_natCast k)
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨(k : ℤ), hwitness⟩

/-- Coercion to the unit additive circle removes a natural-number translate. -/
theorem unitAddCircle_natAdd_eq (k : ℕ) (u : ℝ) :
    (((k : ℝ) + u : ℝ) : UnitAddCircle) = (u : UnitAddCircle) := by
  have hadd :
      (((k : ℝ) + u : ℝ) : UnitAddCircle) =
        (((k : ℝ) : UnitAddCircle) + (u : UnitAddCircle)) :=
    AddCircle.coe_add (1 : ℝ) (k : ℝ) u
  exact Eq.trans hadd
    (Eq.trans
      (congrArg (fun z : UnitAddCircle => z + (u : UnitAddCircle))
        (unitAddCircle_natCast_eq_zero k))
      (zero_add (u : UnitAddCircle)))

/-- Every canonical centered-quadratic Fourier mode is one-periodic under
natural-number translations. -/
theorem centeredQuadraticPrimitiveFourierMode_natAdd
    (m : ℤ)
    (k : ℕ)
    (u : ℝ) :
    centeredQuadraticPrimitiveFourierMode m ((k : ℝ) + u) =
      centeredQuadraticPrimitiveFourierMode m u := by
  unfold centeredQuadraticPrimitiveFourierMode
  exact congrArg
    (fun z : ℂ => ((1 : ℂ) / (m : ℂ) ^ (2 : ℕ)) * z)
    (congrArg (fun z : UnitAddCircle => fourier m z)
      (unitAddCircle_natAdd_eq k u))

/-- The periodic centered primitive is invariant under natural-number
translations. -/
theorem periodicCenteredQuadraticPrimitive_natAdd
    (k : ℕ)
    (u : ℝ) :
    periodicCenteredQuadraticPrimitive ((k : ℝ) + u) =
      periodicCenteredQuadraticPrimitive u := by
  have hterms :
      (fun m : ℤ =>
        centeredQuadraticPrimitiveFourierMode m ((k : ℝ) + u)) =
        (fun m : ℤ => centeredQuadraticPrimitiveFourierMode m u) := by
    funext m
    exact centeredQuadraticPrimitiveFourierMode_natAdd m k u
  unfold periodicCenteredQuadraticPrimitive
  exact congrArg
    (fun z : ℂ => (centeredQuadraticPrimitiveFourierNormalization)⁻¹ * z)
    (congrArg (fun f : ℤ → ℂ => ∑' m : ℤ, f m) hterms)

/-- On each translated unit block, the periodic centered primitive is the
centered quadratic polynomial in the local coordinate. -/
theorem periodicCenteredQuadraticPrimitive_natAdd_eq
    (k : ℕ)
    {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    periodicCenteredQuadraticPrimitive ((k : ℝ) + u) =
      (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u : ℂ) :=
  Eq.trans
    (periodicCenteredQuadraticPrimitive_natAdd k u)
    (periodicCenteredQuadraticPrimitive_eq hu)

/-- Subtracting the exact Bernoulli moment from the periodic centered
primitive recovers the zero-endpoint quadratic primitive on every unit block. -/
theorem periodicCenteredQuadraticPrimitive_natAdd_sub_one_twelfth_eq
    (k : ℕ)
    {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    periodicCenteredQuadraticPrimitive ((k : ℝ) + u) - (1 / 12 : ℂ) =
      eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex u := by
  have hperiodic := periodicCenteredQuadraticPrimitive_natAdd_eq k hu
  have hreal :
      eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u -
          (1 / 12 : ℝ) =
        eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u :=
    add_sub_cancel_right
      (eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u)
      (1 / 12 : ℝ)
  have hcast :
      (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u : ℂ) -
          (1 / 12 : ℂ) =
        (eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u : ℂ) := by
    have hcastOneTwelfth : (((1 / 12 : ℝ) : ℂ)) = (1 / 12 : ℂ) := by
      exact Complex.ofReal_div (1 : ℝ) (12 : ℝ)
    calc
      (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u : ℂ) -
          (1 / 12 : ℂ) =
          (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u : ℂ) -
            (((1 / 12 : ℝ) : ℂ)) := by
        exact congrArg
          (fun z : ℂ =>
            (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u : ℂ) - z)
          hcastOneTwelfth.symm
      _ = ((eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u -
          (1 / 12 : ℝ) : ℝ) : ℂ) :=
        (map_sub Complex.ofRealHom
          (eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitive u)
          (1 / 12 : ℝ)).symm
      _ = (eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitive u : ℂ) :=
        congrArg (fun r : ℝ => (r : ℂ)) hreal
  unfold eulerMaclaurinFirstPeriodicBernoulliQuadraticPrimitiveComplex
  exact Eq.trans
    (congrArg (fun z : ℂ => z - (1 / 12 : ℂ)) hperiodic)
    hcast

end
end LFunctions
end Boundary
