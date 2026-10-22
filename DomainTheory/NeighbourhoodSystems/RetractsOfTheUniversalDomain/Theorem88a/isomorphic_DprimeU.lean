/-ai
The neighbourhood system D is isomorphic, as a domain, to the system DprimeU built from the enumeration e.

The isomorphism is the domain isomorphism associated with D, e, the covering, and the convention that e 0 is the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Basic.Countable.Defs
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}


section Iso

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)


/-- **First sentence of Theorem 8.8 (isomorphism half).** `D ≅ᴰ D'`. -/
theorem isomorphic_DprimeU : D ≅ᴰ DprimeU D e hcover he0 := ⟨domainIso D e hcover he0⟩

end Iso
end DomainTheory.NeighbourhoodSystems
