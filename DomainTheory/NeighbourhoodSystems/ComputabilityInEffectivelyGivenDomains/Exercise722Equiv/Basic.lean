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

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set


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


end Exercise722
end DomainTheory.NeighbourhoodSystems
