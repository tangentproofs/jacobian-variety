import Jacobian.AbelJacobi.WitnessMk
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Symmetry / sign identities for `witnessAbelJacobi` / `evalJacobianClass`

A few extra simp-friendly identities derived from the existing
algebra of the witness map.
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- Negating the vector flips the witness sign (alias). -/
theorem witnessAbelJacobi_neg_vec_eq_neg
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P (-v) =
      -witnessAbelJacobi basePoint P v :=
  witnessAbelJacobi_neg_vec basePoint P v

/--
Negating both endpoints of `evalJacobianClass` (via vec-slot
negation) flips the class.
-/
theorem evalJacobianClass_neg_vec_at_endpoint
    (P : X) (v : E) :
    evalJacobianClass (E := E) (X := X) P (-v) =
      -evalJacobianClass P v :=
  evalJacobianClass_neg_vec P v

/-- Doubling the witness via vec-doubling. -/
theorem witnessAbelJacobi_two_smul_vec
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P (2 • v) =
      2 • witnessAbelJacobi basePoint P v :=
  witnessAbelJacobi_nsmul_vec basePoint P 2 v

/--
The witness is `0` whenever `evalLinearMap` agrees on the two
endpoints.
-/
theorem witnessAbelJacobi_eq_zero_of_evalLinearMap_eq
    (basePoint P : X) (v : E)
    (h : evalLinearMap (E := E) (X := X) P v = evalLinearMap basePoint v) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 := by
  rw [witnessAbelJacobi_eq_mk_sub, h, sub_self, mk_zero]

end JacobianChallenge.AbelJacobi
