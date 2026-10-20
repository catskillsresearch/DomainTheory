module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap





universe u

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **"Be sure to show that this result has the right type."** `translateAbs a b body` always
satisfies the defining sandwich equation `f = b∘f∘a` of Scott's `D_a → D_b` translation scheme
(the "sense defined above" — see `Proposition810b.elementIsoOfProjectionPair`/
`arrowComb_elementIso`), **regardless of `body`** — the *only* thing this uses is idempotence of
`a` and `b` (true of every retraction, Definition 8.1, in particular every finitary projection,
Definition 8.3). Pure associativity + idempotence, mirroring the book's own one-line proof
("`(a×b)∘(a×b) = ... = a×b`," `Proposition 8.10`'s proof) transplanted to the abstraction case. -/
theorem translateAbs_sandwich {a b body : ApproximableMap E E}
    (ha : IsRetraction a) (hb : IsRetraction b) :
    b.comp ((translateAbs a b body).comp a) = translateAbs a b body := by
  show b.comp ((b.comp (body.comp a)).comp a) = b.comp (body.comp a)
  rw [comp_assoc b (body.comp a) a, comp_assoc body a a, ha, ← comp_assoc b b (body.comp a), hb]

end DomainTheory.NeighbourhoodSystems
