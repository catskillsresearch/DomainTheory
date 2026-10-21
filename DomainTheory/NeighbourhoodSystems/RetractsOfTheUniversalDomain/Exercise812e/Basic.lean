/-ai
This file gathers and re-exports the computable bisection, the positive and negative index functions, the classical split built from a bisection, the proof that this split is computable, the set-congruence of the two emptiness deciders, the primitive recursiveness of the two index functions, and the unfolding of the split on a presented triple.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.ComputableBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.posIdxFromBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.negIdxFromBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.splitFromBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.isComputableSplit_ofBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.emptyInterDec_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.emptyDiffDec_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.primrec_posIdxFromBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.primrec_negIdxFromBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.splitFromBisection_eq

@[expose] public section

/-!
# Exercise 8.12(e) (Scott 1981, PRG-19, Lecture VIII) — `U` satisfies the extension property
relative to `V`

## 8.12(e)(a): the split's contract, as Lean declarations

`(d)`'s `IsComputableSplit P Q split` structure only ever gets *consumed*, downstream, through its
two index functions `posIdx`/`negIdx : ℕ → ℕ → ℕ → ℕ` (`xSubStep`/`ySubStep`, `Exercise812d.lean`).
This section fixes the *design* for those two functions concretely, as genuine `Nat`-valued `def`s
(no proof obligations yet — those are `(e)(c)`'s job): given a prober presentation `P` (with an
`IsComputableDiff` witness) and a target presentation `Q` equipped with a computable canonical
bisection (`ComputableBisection`, below), decide via the prober's own `emptyInterDec`/`emptyDiffDec`
deciders ((d)(2)) whether the "chosen branch" is (as far as these two deciders can tell) forced
empty, and fall back to the bisection only when neither decider fires.

Both `posIdxFromBisection`/`negIdxFromBisection` share the same outer shape and, not entirely
obviously, the same "either decider fires" branch value `m` (i.e. literally `B` itself) — one of the
two decider branches is the *genuinely correct* value in that case (`A ⊆ Xn` resp. `Xn ∩ A = ∅`
forces the corresponding piece to be exactly `B`), the other is a harmless placeholder that later
gets junk-masked (`xSubStep`'s `newJunk`) before ever being read — see the `(e)(a)` row of
`arxiv.md` for the case-by-case argument. Only the "both deciders silent" branch genuinely bisects
`B`, via the supplied `ComputableBisection`. -/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)



/-! ### 8.12(e)(c)(i): decider congruence and index-function well-definedness

`emptyInterDec`/`emptyDiffDec` depend only on the *sets* `P.X n ∩ P.X k`/`P.X n \ P.X k` (via
`(d)(2)`'s `_eq_one_iff` characterizations), not on which raw index presents them — and, combined
with `left_congr`/`right_congr` above, this transports all the way up to `posIdxFromBisection`/
`negIdxFromBisection` being well-defined functions of sets, exactly what `(e)(c)(ii)`'s
`posIdx_spec`/`negIdx_spec` will need. -/

section Congr

variable {n n' k k' m m' : ℕ}



end Congr

/-! ### 8.12(e)(c)(ii): `splitFromBisection` and `isComputableSplit_ofBisection`

The actual classical split, and its `IsComputableSplit` proof, completing `8.12(e)(c)`. Genuinely
new work beyond `(e)(c)(i)`: the two index functions' *joint* primitive-recursiveness (as a single
function of the packed triple `Nat.pair n (Nat.pair m k)`, `IsComputableSplit`'s own convention) was
not yet proved — `posIdxFromBisection`/`negIdxFromBisection` are primitive recursive in each
*argument* separately (from their own defining pieces) but had not yet been packaged as one
triple-argument `Nat.Primrec` witness. **Deviation from the `arxiv.md` draft signature**:
`splitFromBisection` itself takes only `P`, `hDiff`, `B` (not `hpos`/`hnomin`/`hdiffClosed`) — those
three hypotheses are needed only for *correctness* (`isComputableSplit_ofBisection`'s `posIdx_spec`/
`negIdx_spec`, via `(e)(c)(i)`'s congruence lemmas), never for the definition itself, mirroring how
`posIdxFromBisection`/`negIdxFromBisection` are themselves already hypothesis-free to *define*. -/





end ComputableBisection
end DomainTheory.NeighbourhoodSystems
