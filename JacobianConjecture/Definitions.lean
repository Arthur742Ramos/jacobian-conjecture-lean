import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Definitions for an explicit Jacobian-conjecture counterexample

The definitions in this file are deliberately proof-free.  They give the
ordinary multivariate-polynomial Jacobian, its determinant, evaluation of a
polynomial self-map, and the explicit map used by the advertised theorem.
-/

noncomputable section

open Matrix Function

namespace MvPolynomial

variable {R : Type*} {σ : Type*}

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
