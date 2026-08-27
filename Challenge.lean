import JacobianConjecture.Definitions
import Mathlib.Data.Complex.Basic

open Function

/-!
# Advertised statement

This is the small statement surface for an explicit counterexample to the
Jacobian conjecture. The definitions are ordinary multivariate polynomials;
the proof is supplied separately in `Solution.lean` and checked by Comparator.
-/

variable (K : Type*) [Field K]

/-- The formal determinant of the announced map is the constant polynomial `-2`. -/
theorem JacobianCounterexample.jacobianDet_F :
    MvPolynomial.jacobianDet (JacobianCounterexample.F K) =
      MvPolynomial.C (-2) := by
  sorry

variable {K}

/-- Three explicit rational points lie in one fibre of the map over `ℂ`. -/
theorem JacobianCounterexample.explicit_three_point_fibre :
    MvPolynomial.evalMap (JacobianCounterexample.F ℂ)
        ![0, 0, -(1 / 4)] = ![-(1 / 4), 0, 0] ∧
      MvPolynomial.evalMap (JacobianCounterexample.F ℂ)
        ![1, -(3 / 2), 13 / 2] = ![-(1 / 4), 0, 0] ∧
      MvPolynomial.evalMap (JacobianCounterexample.F ℂ)
        ![-1, 3 / 2, 13 / 2] = ![-(1 / 4), 0, 0] := by
  sorry

/-- The dimension-three Jacobian conjecture is false over the complex numbers. -/
theorem JacobianCounterexample.not_jacobian_conjecture_complex :
    ¬ ∀ P : Fin 3 → MvPolynomial (Fin 3) ℂ,
      IsUnit (MvPolynomial.jacobianDet P) →
        Injective (MvPolynomial.evalMap P) := by
  sorry
