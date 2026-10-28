import Jacobian.AbelJacobi.WitnessZeroIff
import Jacobian.AnalyticJacobian.MkPeriodPairingSmul
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Sufficient witness-zero conditions via integer-scaled `periodPairing`

Continues `WitnessZeroIff` with sufficient conditions in which the
endpoint difference is an integer-scaled `periodPairing` value, plus
the negation variant. Each composes
`witnessAbelJacobi_eq_mk_sub` with the matching
`mk_{n,z}smul_periodPairing` / `mk_neg_periodPairing` collapse.
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/--
Sufficient: endpoint diff = `n • periodPairing E X σ` (`n : ℕ`)
implies the witness is zero.
-/
theorem witnessAbelJacobi_eq_zero_of_endpoint_diff_eq_nsmul_periodPairing
    (basePoint P : X) (v : E) (n : ℕ) (σ : IntegralOneCycle X)
    (h : evalLinearMap P v - evalLinearMap basePoint v =
        n • periodPairing E X σ) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 := by
  rw [witnessAbelJacobi_eq_mk_sub, h, mk_nsmul_periodPairing]

/--
Sufficient: endpoint diff = `n • periodPairing E X σ` (`n : ℤ`)
implies the witness is zero.
-/
theorem witnessAbelJacobi_eq_zero_of_endpoint_diff_eq_zsmul_periodPairing
    (basePoint P : X) (v : E) (n : ℤ) (σ : IntegralOneCycle X)
    (h : evalLinearMap P v - evalLinearMap basePoint v =
        n • periodPairing E X σ) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 := by
  rw [witnessAbelJacobi_eq_mk_sub, h, mk_zsmul_periodPairing]

/--
Sufficient: endpoint diff = `-periodPairing E X σ` implies the
witness is zero.
-/
theorem witnessAbelJacobi_eq_zero_of_endpoint_diff_eq_neg_periodPairing
    (basePoint P : X) (v : E) (σ : IntegralOneCycle X)
    (h : evalLinearMap P v - evalLinearMap basePoint v =
        -periodPairing E X σ) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 := by
  rw [witnessAbelJacobi_eq_mk_sub, h, mk_neg_periodPairing]

/--
Sufficient: a `periodPairing` value placed via `(n : ℤ) • _` for
`n : ℕ` (cast version), mostly useful when downstream code carries
`ℤ`-typed scalars naturally.
-/
theorem witnessAbelJacobi_eq_zero_of_endpoint_diff_eq_natCast_zsmul_periodPairing
    (basePoint P : X) (v : E) (n : ℕ) (σ : IntegralOneCycle X)
    (h : evalLinearMap P v - evalLinearMap basePoint v =
        (n : ℤ) • periodPairing E X σ) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 :=
  witnessAbelJacobi_eq_zero_of_endpoint_diff_eq_zsmul_periodPairing
    basePoint P v (n : ℤ) σ h

end JacobianChallenge.AbelJacobi
