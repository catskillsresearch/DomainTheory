/-ai
Scott's second example is an information system whose tokens are strict integer intervals, read as open bounds on a rational, together with a least-informative token read as always true. Consistency means that some rational satisfies every token of the finite set, and entailment means that every rational satisfying the set satisfies the token. The example builds that system from the satisfaction relation, using that the least token is always satisfied and that every token is satisfiable.
ai-/
module

public import Mathlib.Algebra.Order.Field.Rat
import all Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
import all Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
import all Mathlib.Tactic.NormNum
public import DomainTheory.InformationSystems.InformationSystems.InfoSys

public import DomainTheory.InformationSystems.InformationSystems.Factoid25.Token
public import DomainTheory.InformationSystems.InformationSystems.Sat
public import DomainTheory.InformationSystems.InformationSystems.ofSatisfaction
public import DomainTheory.InformationSystems.InformationSystems.instDecidableEq
public import DomainTheory.InformationSystems.InformationSystems.sat_midpoint
public import DomainTheory.InformationSystems.InformationSystems.sat_sing

@[expose] public section

/-!
# Factoid 2.5 — second example: open intervals plus `(0, ∞)`

**Scott 1982, §2 (“A second example”).** Data objects are pairs `(n, m)` of integers
with `n < m`, read as `n < x < m`, together with an artificial least-informative
object `(0, ∞)` (our `bot`). Consistency: some point satisfies every token in the
finite set. Entailment: every point satisfying the left-hand set satisfies the
right-hand token.

We take the point space to be `ℚ` so every strict integer-endpoint interval is
inhabited (Def 2.1(ii)). The always-true reading of `bot` matches Scott’s
“artificial” Δ.
-/

namespace DomainTheory.InformationSystems

namespace Factoid25

namespace Token


end Token





/-- **Factoid 2.5.** Interval information system of Scott 1982, §2. -/
example : InfoSys Token :=
  ofSatisfaction Sat Token.bot (fun _ => trivial) sat_sing

end Factoid25

end DomainTheory.InformationSystems
