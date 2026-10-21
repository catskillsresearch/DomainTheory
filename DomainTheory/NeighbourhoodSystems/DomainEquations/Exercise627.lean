/-ai
This file gathers and re-exports the results of Exercise 6.27. It re-exports the basic development, the proof that the smash product is a subsystem of the product and therefore embeds in it, the first-factor projection pair and the embedding of a domain in its product, the proof that the coalesced sum is a subsystem of the separated sum and therefore embeds in it, the strictification inequalities, the representation identities for approximable maps, filters, strict maps, and strict filters, the element-map computations for inclusion and strictification, the projection-pair laws and the embedding of the strict function space in the function space, extensionality from agreement on principal inputs, and the collapse of the smash with the one-point unit, which shows that a domain need not embed in a smash product.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.otimesTok_subsystem_prodTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.otimes_trianglelefteq_prod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.fstProj_comp_fstInj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.fstInj_comp_fstProj_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.fst_trianglelefteq_prod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.oplusTok_subsystem_sumTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.oplus_trianglelefteq_sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strictifyMap_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strictifyMap_of_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.toApproxMap_toFilter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.toFilter_toApproxMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.toStrictMap_toStrictFilter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.toStrictFilter_toStrictMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.toElementMap_inclMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.toElementMap_strctMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strct_incl
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.incl_strct_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.ext_of_principal
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strctMap_comp_inclMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.inclMap_comp_strctMap_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strictFun_trianglelefteq_funSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.subsingleton_element_of_only_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.otimes_unitPt_collapse
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.not_trianglelefteq_otimes

@[expose] public section
