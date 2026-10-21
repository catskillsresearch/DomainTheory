/-ai
This file gathers and re-exports the sequence-domain maps of Exercise 5.16 together with the comparison theorems for those maps. It re-exports extensionality of maps out of the domain of binary sequences, the tail equations after a cons, the recursion equations for bit-complement on the two bits, the involution law for complement, and the diagonal laws for the interleaving value and the interleaved element. It also re-exports the representation of neighbourhoods by tagged shapes, extensionality of maps out of a product, the pairing law for principal neighbourhoods, and the recursion and diagonal equations for the merge map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.map_ext_C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_consMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_consMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.neg_cons_false
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.neg_cons_true
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap_comp_negMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap_negMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeVal_diag
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeElem_diag
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeMap_pair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.memC_eq_shape
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.prod_principal_pair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.prodMap_ext
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeMap_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeMap_diag

@[expose] public section
