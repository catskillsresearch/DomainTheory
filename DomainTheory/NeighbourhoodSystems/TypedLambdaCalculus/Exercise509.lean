/-ai
This file gathers and re-exports the development of Exercise 5.9: elementwise commutation, the least common fixed point of two commuting maps, the zero and successor laws for iteration from the bottom element, the inequality of those iterates below the least fixed point, equality of least fixed points when commuting maps agree at the bottom element, iteration of a square, and equality of the least fixed point of a map with the least fixed point of its square.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.commute_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.commuting_least_common_fixed
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.iterElem_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.iterElem_zerou27
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.fixElement_eq_of_commuting_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.iterElem_le_fixElement
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.comp_self_iterElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.fixElement_iterTwice

@[expose] public section
