/-ai
If g composed with the cons map equals k composed with the product of the identity and g, then g composed with the successor truncation equals the descent operator of k applied to g composed with the previous truncation.

The successor truncation unfolds as the cons map after the product of the identity with the previous truncation, after the splitting map. The assumed equation replaces g after the cons map by k after that product. Reassociating, using that a product of composites is the composite of the products, and using that the identity composed with itself is the identity, gives the descent operator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.jmap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.imap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descOp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Uniq

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- **`g`-independence step.** If `g` is a homomorphism (`g ∘ i = k ∘ T(g)`) then
`g ∘ ρₙ₊₁ = k ∘ T(g ∘ ρₙ) ∘ j = Op_k(g ∘ ρₙ)`: the composite depends only on `g ∘ ρₙ`. -/
theorem gcomp_rho_succ (k : ApproximableMap (prod V E) E) (g : ApproximableMap (iterSys V) E)
    (hc : g.comp (imap V) = k.comp (prodMap (idMap V) g)) (n : ℕ) :
    g.comp (descSeq (imap V) (n + 1)) = descOp k (g.comp (descSeq (imap V) n)) := by
  show g.comp ((imap V).comp ((prodMap (idMap V) (descSeq (imap V) n)).comp (jmap V)))
     = k.comp ((prodMap (idMap V) (g.comp (descSeq (imap V) n))).comp (jmap V))
  rw [← comp_assoc, hc, comp_assoc]
  congr 1
  rw [← comp_assoc, ← prodMap_comp, idMap_comp]

end Uniq

end Exercise618

end DomainTheory.NeighbourhoodSystems
