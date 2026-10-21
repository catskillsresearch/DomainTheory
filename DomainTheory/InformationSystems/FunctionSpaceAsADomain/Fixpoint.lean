/-ai
This module gathers and re-exports the least-fixed-point results of Scott's Theorem 7.3: the basic relation lemma, the inclusion of fix chains in a pre-fixed point, the least-pre-fixed-point inequality, the one-step extension of a chain, the inequality for the operator applied to the fixed point, the fixed-point equation, uniqueness of the fixed-point element, and uniqueness of the approximable fixed-point map.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_subset_pre_fixed
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement_le_of_pre_fixed
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_step_of_rel
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.toElement_fixElement_le
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement_fixed
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement_unique
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixMap_unique

@[expose] public section
