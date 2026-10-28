import Jacobian.TraceDegree.PullbackFormsLinearMap
import Jacobian.TraceDegree.PullbackFun
import Jacobian.TraceDegree.PullbackFunComp
import Jacobian.TraceDegree.PullbackFunId
import Jacobian.TraceDegree.PullbackFunSmul

/-!
# Trace, degree, pushforward, pullback infrastructure

**Notes:**
- `PullbackFun` defines `pullbackFormsFun` (the chain-rule pullback
  at the function level) plus zero/neg/add linearity. The smoothness
  upgrade to `HolomorphicOneForm E X` is intentionally a follow-up.
-/
