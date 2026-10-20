module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.acceptFin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.startFin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.stepFinSingle
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.stepFin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.evalFin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.diffNFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.subsetB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.interEqB

@[expose] public section

/-!
# Exercise 7.22k — language equivalence via a `Finset`-valued subset construction (Session C7b)

`toNFA e : NFA Bool (autState e)` is genuinely nondeterministic once `.cat` is involved (the
concatenation automaton's ε-closure fans a single state out to several live states), so deciding
`denote e₁ = denote e₂` cannot be reduced to a simple bounded search over `matchesB` alone:
"`e₂` rejects `w`" is a *universal* statement over `e₂`'s nondeterministic paths, and universal
statements over NFA paths don't pump the way existential ones do (`exists_accepted_word_short`).

The fix is a **choice-free `Finset`-valued subset-construction simulation** of `toNFA e`: track the
*entire* set of live NFA states as a `Finset (autState e)` (decidable, since `autState e` already
carries `Fintype`/`DecidableEq`, `Exercise722Decide.lean`), evolving **deterministically**. Once
both `e₁`'s and `e₂`'s live-state-sets are tracked simultaneously (as one `Finset`-pair state), the
question "is there a word `e₁` accepts but `e₂` rejects" becomes an ordinary NFA-emptiness question
on a *deterministic* (singleton-step) NFA, to which `exists_accepted_word_short` applies directly.
-/

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set

/-! ## `Finset`-valued simulation of `toNFA e`

`acceptFin`/`startFin`/`stepFinSingle` mirror `toNFA`'s own recursive cases exactly, computing the
same sets as `Finset`s (decidable data) instead of `Set`s. Correctness (`coe_acceptFin` etc.) shows
each agrees with `toNFA e`'s actual `Set`-valued semantics. -/


theorem coe_acceptFin : ∀ e : SExpr, (↑(acceptFin e) : Set (autState e)) = (toNFA e).accept
  | .sigma => by
      show (↑(Finset.univ : Finset Unit) : Set Unit) = sigmaDFA.toNFA.accept
      show (↑(Finset.univ : Finset Unit) : Set Unit) = Set.univ
      ext x; cases x; simp
  | .single σ => by
      change (↑({(some ⟨σ.length, Nat.lt_succ_self _⟩ : SingleState σ)} : Finset _) : Set _)
        = (singleDFA σ).toNFA.accept
      simp [DFA.toNFA, singleDFA]
  | .cap a b => by
      change (↑((acceptFin a) ×ˢ (acceptFin b)) : Set (autState a × autState b))
        = (NFAinter (toNFA a) (toNFA b)).accept
      rw [Finset.coe_product, coe_acceptFin a, coe_acceptFin b]
      rfl
  | .cat a b => by
      show (↑((acceptFin b).image (inr : autState b → autState a ⊕ autState b)) :
        Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.accept
      show (↑((acceptFin b).image (inr : autState b → autState a ⊕ autState b)) :
        Set (autState a ⊕ autState b)) = inr '' (toNFA b).accept
      rw [Finset.coe_image, coe_acceptFin b]





/-! ## The "difference" automaton: `e₁` is live and `e₂` is dead

Tracks `e₁`'s and `e₂`'s live-state `Finset`s *simultaneously* as one deterministic (singleton
step/start) NFA, so `exists_accepted_word_short` — genuinely generic over any `Fintype` NFA state
space — bounds the length of a shortest word witnessing `denote e₁ ⊄ denote e₂`. -/


/-! ## Bounded-word-search deciders for `⊆` and `=` -/


end Exercise722
end DomainTheory.NeighbourhoodSystems
