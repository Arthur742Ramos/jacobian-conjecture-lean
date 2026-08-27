import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Function

noncomputable section

namespace MvPolynomial

variable {R : Type*} {σ : Type*}

/-! These definitions are repeated here so the challenge can be audited and
compiled without importing project-specific source. -/

/-- The formal Jacobian matrix of a family of multivariate polynomials. -/
def jacobianMatrix [CommSemiring R] [DecidableEq σ]
    (F : σ → MvPolynomial σ R) : Matrix σ σ (MvPolynomial σ R) :=
  Matrix.of fun i j => pderiv j (F i)

/-- The formal determinant of the Jacobian matrix of `F`. -/
def jacobianDet [CommRing R] [Fintype σ] [DecidableEq σ]
    (F : σ → MvPolynomial σ R) : MvPolynomial σ R :=
  (jacobianMatrix F).det

/-- The polynomial self-map induced by a family of multivariate polynomials. -/
def evalMap [CommSemiring R] (F : σ → MvPolynomial σ R) (p : σ → R) : σ → R :=
  fun i => eval p (F i)

end MvPolynomial

namespace JacobianCounterexample

open MvPolynomial

variable (K : Type*) [Field K]

/-- The three coordinate polynomials of the announced map. -/
def F : Fin 3 → MvPolynomial (Fin 3) K :=
  ![(1 + X 0 * X 1) ^ 3 * X 2 + X 1 ^ 2 * (1 + X 0 * X 1) *
      (C 4 + C 3 * (X 0 * X 1)),
    X 1 + C 3 * X 0 * (1 + X 0 * X 1) ^ 2 * X 2 +
      C 3 * X 0 * X 1 ^ 2 * (C 4 + C 3 * (X 0 * X 1)),
    C 2 * X 0 - C 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2]

end JacobianCounterexample

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

end
