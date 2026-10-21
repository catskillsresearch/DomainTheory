/-ai
If an approximable endomap is computable, then its diagonal fixed-point predicate is recursively enumerable.

The computable map gives a recursively enumerable relation on packed pairs of indices. Composing with the primitive-recursive pairing of an index with itself, and using the unpairing equations, restricts that relation to the diagonal predicate.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


/-- **`DiagFixed P a` is recursively enumerable, given `a` is a computable map.** Restrict
`IsComputableMap`'s two-variable relation `Xₙ a Xₘ` to the diagonal `n = m` via `REPred.comp`
against the primitive-recursive pairing `n ↦ Nat.pair n n`. -/
theorem diagFixed_isREPred {P : ComputablePresentation V} {a : ApproximableMap V V}
    (ha : IsComputableMap P P a) : REPred (DiagFixed P a) := by
  have ha' : REPred (fun t : ℕ => a.rel (P.X t.unpair.1) (P.X t.unpair.2)) := ha
  have hdiag : Nat.Primrec (fun n : ℕ => Nat.pair n n) := primrec_id.pair primrec_id
  refine REPred.of_iff (fun n => ?_) (ha'.comp hdiag)
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact Iff.rfl

end DomainTheory.NeighbourhoodSystems
