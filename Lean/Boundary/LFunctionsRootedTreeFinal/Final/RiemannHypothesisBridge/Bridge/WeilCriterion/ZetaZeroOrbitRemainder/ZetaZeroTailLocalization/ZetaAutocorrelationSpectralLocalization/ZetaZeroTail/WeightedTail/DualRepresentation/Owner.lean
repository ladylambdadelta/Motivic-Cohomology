import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.DualPairing.Owner

/-!
# Discrete completed-zero `l1` dual representation

This owner identifies continuous linear functionals on the completed-zero
coordinate `l1` space with bounded coordinate families.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ENNReal

/-- The discrete completed-zero coordinate `l1` space. -/
abbrev ZetaCompletedZeroCoordinateL1 :=
  lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal)

/-- The unit singleton at a completed-zero coordinate. -/
noncomputable def zetaCompletedZeroCoordinateUnitSingleton
    (rho : ZetaCompletedZeroCoordinate) : ZetaCompletedZeroCoordinateL1 :=
  lp.single (1 : ENNReal) rho (1 : ℂ)

/-- The unit completed-zero singleton has norm one. -/
theorem norm_zetaCompletedZeroCoordinateUnitSingleton
    (rho : ZetaCompletedZeroCoordinate) :
    norm (zetaCompletedZeroCoordinateUnitSingleton rho) = 1 := by
  have hpositiveOne : 0 < (1 : ENNReal).toReal :=
    Eq.mpr
      (congrArg (fun exponent : ℝ => 0 < exponent) ENNReal.one_toReal)
      Real.zero_lt_one
  unfold zetaCompletedZeroCoordinateUnitSingleton
  exact Eq.trans
    (lp.norm_single
      hpositiveOne
      (fun _ : ZetaCompletedZeroCoordinate => (1 : ℂ))
      rho)
    (norm_one : norm (1 : ℂ) = 1)

/-- The coordinate coefficient of a continuous functional on the completed-zero
discrete `l1` space. -/
noncomputable def zetaCompletedZeroSideL1DualCoefficient
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ)
    (rho : ZetaCompletedZeroCoordinate) : ℂ :=
  L (zetaCompletedZeroCoordinateUnitSingleton rho)

/-- The coefficient family of a continuous `l1` functional is bounded by its
operator norm. -/
theorem norm_zetaCompletedZeroSideL1DualCoefficient_le
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ)
    (rho : ZetaCompletedZeroCoordinate) :
    norm (zetaCompletedZeroSideL1DualCoefficient L rho) <= norm L := by
  unfold zetaCompletedZeroSideL1DualCoefficient
  calc
    norm (L (zetaCompletedZeroCoordinateUnitSingleton rho)) <=
        norm L * norm (zetaCompletedZeroCoordinateUnitSingleton rho) :=
      L.le_opNorm (zetaCompletedZeroCoordinateUnitSingleton rho)
    _ = norm L * norm (1 : ℂ) := by
      exact
        congrArg
          (fun value : ℝ => norm L * value)
          (Eq.trans
            (norm_zetaCompletedZeroCoordinateUnitSingleton rho)
            (norm_one : norm (1 : ℂ) = (1 : ℝ)).symm)
    _ = norm L * 1 := by
      exact congrArg (fun value : ℝ => norm L * value) (norm_one : norm (1 : ℂ) = 1)
    _ = norm L := by
      exact mul_one (norm L)

/-- The bounded completed-zero family extracted from a continuous `l1`
functional. -/
noncomputable def zetaCompletedZeroSideL1DualCoefficientFamily
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ) :
    lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal) :=
  ⟨zetaCompletedZeroSideL1DualCoefficient L,
    memℓp_infty
      (by
        exact
          ⟨norm L,
            fun value hvalue =>
              match hvalue with
              | ⟨rho, hcoordinate⟩ =>
                  Eq.mp
                    (congrArg (fun target : ℝ => target ≤ norm L) hcoordinate)
                    (norm_zetaCompletedZeroSideL1DualCoefficient_le L rho)⟩)⟩

/-- The extracted bounded family has the defining coefficient at each coordinate. -/
theorem zetaCompletedZeroSideL1DualCoefficientFamily_apply
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ)
    (rho : ZetaCompletedZeroCoordinate) :
    zetaCompletedZeroSideL1DualCoefficientFamily L rho =
      zetaCompletedZeroSideL1DualCoefficient L rho := by
  rfl

/-- Each singleton coordinate is a scalar multiple of the unit singleton. -/
theorem zetaCompletedZeroSideL1Dual_singleton_coordinate
    (rho : ZetaCompletedZeroCoordinate)
    (a : ℂ) :
    (lp.single (1 : ENNReal) rho a : ZetaCompletedZeroCoordinateL1) =
      a • zetaCompletedZeroCoordinateUnitSingleton rho := by
  unfold zetaCompletedZeroCoordinateUnitSingleton
  have hscalarIdentity : a = a • (1 : ℂ) := by
    calc
      a = a * (1 : ℂ) := (mul_one a).symm
      _ = a • (1 : ℂ) := rfl
  let singletonAt : ℂ → ZetaCompletedZeroCoordinateL1 :=
    fun value =>
      lp.single
        (E := fun _ : ZetaCompletedZeroCoordinate => ℂ)
        (1 : ENNReal)
        rho
        value
  have hsingletonSmul :
      singletonAt (a • (1 : ℂ)) = a • singletonAt (1 : ℂ) := by
    unfold singletonAt
    exact
      lp.single_smul
        (E := fun _ : ZetaCompletedZeroCoordinate => ℂ)
        (𝕜 := ℂ)
        (1 : ENNReal)
        rho
        (1 : ℂ)
        a
  have hsingletonProposition :
      (singletonAt a = a • singletonAt (1 : ℂ)) =
        (singletonAt (a • (1 : ℂ)) = a • singletonAt (1 : ℂ)) :=
    congrArg
      (fun value : ℂ => singletonAt value = a • singletonAt (1 : ℂ))
      hscalarIdentity
  exact Eq.mpr hsingletonProposition hsingletonSmul

/-- Applying a continuous `l1` functional to a coordinate singleton evaluates
as its extracted coefficient times that coordinate. -/
theorem zetaCompletedZeroSideL1Dual_apply_singleton_coordinate
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ)
    (rho : ZetaCompletedZeroCoordinate)
    (a : ℂ) :
    L (lp.single (1 : ENNReal) rho a : ZetaCompletedZeroCoordinateL1) =
      zetaCompletedZeroSideL1DualCoefficient L rho * a := by
  calc
    L (lp.single (1 : ENNReal) rho a) =
        L (a • zetaCompletedZeroCoordinateUnitSingleton rho) := by
      exact congrArg L (zetaCompletedZeroSideL1Dual_singleton_coordinate rho a)
    _ = a • L (zetaCompletedZeroCoordinateUnitSingleton rho) := by
      exact L.map_smul a (zetaCompletedZeroCoordinateUnitSingleton rho)
    _ = a * L (zetaCompletedZeroCoordinateUnitSingleton rho) := rfl
    _ = zetaCompletedZeroSideL1DualCoefficient L rho * a := by
      exact mul_comm a (zetaCompletedZeroSideL1DualCoefficient L rho)

/-- Mapping the canonical singleton expansion of an `l1` vector through a
continuous functional gives its coordinate-series expansion. -/
theorem hasSum_zetaCompletedZeroSideL1Dual_coordinateExpansion
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ)
    (x : ZetaCompletedZeroCoordinateL1) :
    HasSum
      (fun rho : ZetaCompletedZeroCoordinate =>
        zetaCompletedZeroSideL1DualCoefficient L rho * x rho)
      (L x) := by
  have hsingle :
      HasSum
        (fun rho : ZetaCompletedZeroCoordinate =>
          lp.single (1 : ENNReal) rho (x rho))
        x := by
    exact lp.hasSum_single ENNReal.one_ne_top x
  have hmapped :
      HasSum
        (fun rho : ZetaCompletedZeroCoordinate =>
          L (lp.single (1 : ENNReal) rho (x rho)))
        (L x) := by
    exact hsingle.map L L.continuous
  have htermEq :
      (fun rho : ZetaCompletedZeroCoordinate =>
        L (lp.single (1 : ENNReal) rho (x rho))) =
      (fun rho : ZetaCompletedZeroCoordinate =>
        zetaCompletedZeroSideL1DualCoefficient L rho * x rho) := by
    funext rho
    exact zetaCompletedZeroSideL1Dual_apply_singleton_coordinate L rho (x rho)
  have hseriesProposition :
      HasSum
          (fun rho : ZetaCompletedZeroCoordinate =>
            L (lp.single (1 : ENNReal) rho (x rho)))
          (L x) =
        HasSum
          (fun rho : ZetaCompletedZeroCoordinate =>
            zetaCompletedZeroSideL1DualCoefficient L rho * x rho)
          (L x) :=
    congrArg
      (fun series : ZetaCompletedZeroCoordinate → ℂ => HasSum series (L x))
      htermEq
  exact Eq.mp hseriesProposition hmapped

/-- The coefficient family reconstructed from a continuous functional represents
that functional under the completed-zero endpoint pairing. -/
theorem zetaCompletedZeroSideL1DualCoefficientFamily_pairing
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ)
    (x : ZetaCompletedZeroCoordinateL1) :
    L x =
      zetaCompletedZeroSideL1DualPairing
        (zetaCompletedZeroSideL1DualCoefficientFamily L)
        x := by
  have hexpansion :
      HasSum
        (fun rho : ZetaCompletedZeroCoordinate =>
          zetaCompletedZeroSideL1DualCoefficient L rho * x rho)
        (L x) :=
    hasSum_zetaCompletedZeroSideL1Dual_coordinateExpansion L x
  have hseriesEquality :
      (fun rho : ZetaCompletedZeroCoordinate =>
        zetaCompletedZeroSideL1DualCoefficient L rho * x rho) =
        (fun rho : ZetaCompletedZeroCoordinate =>
          zetaCompletedZeroSideL1DualCoefficientFamily L rho * x rho) := by
    funext rho
    exact
      congrArg
        (fun coefficient : ℂ => coefficient * x rho)
        (zetaCompletedZeroSideL1DualCoefficientFamily_apply L rho).symm
  have hfamilyExpansion :
      HasSum
          (fun rho : ZetaCompletedZeroCoordinate =>
            zetaCompletedZeroSideL1DualCoefficientFamily L rho * x rho)
          (L x) := by
    have hseriesProposition :
        HasSum
            (fun rho : ZetaCompletedZeroCoordinate =>
              zetaCompletedZeroSideL1DualCoefficient L rho * x rho)
            (L x) =
          HasSum
            (fun rho : ZetaCompletedZeroCoordinate =>
              zetaCompletedZeroSideL1DualCoefficientFamily L rho * x rho)
            (L x) :=
      congrArg
        (fun series : ZetaCompletedZeroCoordinate → ℂ => HasSum series (L x))
        hseriesEquality
    exact Eq.mp hseriesProposition hexpansion
  unfold zetaCompletedZeroSideL1DualPairing
  exact hfamilyExpansion.tsum_eq.symm

/-- Every continuous linear functional on the discrete completed-zero `l1`
space is represented by a bounded completed-zero coordinate family. -/
theorem exists_zetaCompletedZeroSideL1DualRepresentation
    (L : ZetaCompletedZeroCoordinateL1 →L[ℂ] ℂ) :
    ∃ b : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal),
      ∀ x : lp (fun _ : ZetaCompletedZeroCoordinate => ℂ) (1 : ENNReal),
        L x = zetaCompletedZeroSideL1DualPairing b x := by
  exact
    ⟨zetaCompletedZeroSideL1DualCoefficientFamily L,
      fun x => zetaCompletedZeroSideL1DualCoefficientFamily_pairing L x⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
