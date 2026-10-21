/-ai
This file gathers and re-exports the worked example of the S-expression domain: the identification of its right-hand side with a sum of a product, the unfolding of atom tokens, membership of an atom token in the closure of its singleton, the fold and unfold actions of the domain-equation isomorphism, the existence of the neighbourhood, ideal, and domain-equation isomorphisms, and the action of the identity Scott-continuous map on elements.
ai-/
module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexRhs_eq_sum_product
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexUnfold_atom
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexAtom_mem_self
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexDomainEquationIso_unfold
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexDomainEquationIso_fold
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.exists_sexNeighborhoodIso
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.exists_sexIdealIso
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.exists_sexDomainEquationIso
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexId_toElement

@[expose] public section
