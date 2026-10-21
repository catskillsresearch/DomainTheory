/-ai
This file gathers and re-exports Scott's Theorem 7.2: the equality of repackaging a function token, membership in the element of an approximable map, the two inverse comparisons of approximable maps with function-space elements, the union laws for the left and right lifts, the projection laws for paired elements, membership of first and second components of a subset of a pair, the subset lemmas for left, right, and paired lifts, the evaluation law for application, the uncurry-curry equation, uniqueness of currying, and the statement that approximable maps are exactly the elements of the function space.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mkFunToken_eq
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mem_approxMap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.element_toApproxMap_approxMap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.approxMap_toElement_element_toApproxMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.liftLeft_funion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.liftRight_funion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.fstMap_pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.sndMap_pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mem_fst_of_subset_pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mem_snd_of_subset_pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.subset_pairElements_liftLeft
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.subset_pairElements_liftRight
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.subset_pairElements_liftPair
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.applyMap_toElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.uncurry_curryMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.curryMap_unique
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.theorem_7_2

@[expose] public section
