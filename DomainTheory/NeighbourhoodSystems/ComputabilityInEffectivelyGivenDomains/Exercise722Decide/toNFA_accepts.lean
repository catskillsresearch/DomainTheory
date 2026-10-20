module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.NFAinter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.NFAinter_mem_accepts_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.dfaToNFA_accepts
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.toNFA

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

/-- **The automaton recognises exactly the language it should.** -/
theorem toNFA_accepts : (e : SExpr) → (toNFA e).accepts = denote e
  | .sigma => by
      change sigmaDFA.toNFA.accepts = denote .sigma
      rw [dfaToNFA_accepts sigmaDFA, sigmaDFA_accepts, denote_sigma]
  | .single σ => by
      change (singleDFA σ).toNFA.accepts = denote (.single σ)
      rw [dfaToNFA_accepts (singleDFA σ)]
      exact singleDFA_accepts_denote σ
  | .cap a b => by
      ext x
      change x ∈ (NFAinter (toNFA a) (toNFA b)).accepts ↔ _
      rw [NFAinter_mem_accepts_iff, toNFA_accepts a, toNFA_accepts b, denote_cap]
      exact (Set.mem_inter_iff x (denote a) (denote b)).symm
  | .cat a b => by
      change (catEps (toNFA a) (toNFA b)).toNFA.accepts = denote (.cat a b)
      rw [εNFA.toNFA_correct, catEps_accepts, toNFA_accepts a, toNFA_accepts b, denote_cat]

end Exercise722

end DomainTheory.NeighbourhoodSystems
