/-ai
This file gathers and re-exports the setting of Factoid 7.5 together with the inequality for the strictified element map, emptiness of the function-token image of the empty set, the failures of entailment between the true and false tokens and of empty entailment of their singletons, the values of the conditional on the true and false elements, the round trip of the conditional on a pair, the singleton entailment lemmas for true and false, uniqueness of the conditional, and the isomorphism between the product and the strict function space out of BOOL.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictify_toElement_le
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset_empty
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.not_ent_tru_fls
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.not_ent_fls_tru
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.not_emptyEntails_singleton_tru
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.not_emptyEntails_singleton_fls
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap_toElement_boolTrue
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap_toElement_boolFalse
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap_pair_roundtrip
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.entSet_singleton_tru_of_ent_tru
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.entSet_singleton_fls_of_ent_fls
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap_unique
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.conditional_iso

@[expose] public section
