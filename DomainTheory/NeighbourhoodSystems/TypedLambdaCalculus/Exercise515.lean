/-ai
This file gathers and re-exports the free-semigroup calculation of Exercise 5.15. It re-exports associativity and both distributivity laws for the pointwise product, membership in the star and the unfolding equation of the star, the fixed-point identity and the prefix lemma for a star product, and Arden's lemma. It also re-exports the powers and the star of a singleton, the least solution of the single linear equation on a monoid and on the free monoid of binary words, the two component equations of David Park's solution, and the existence and leastness of that solution.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.smul_assoc
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.sunion_mul
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.smul_union
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.mem_star
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.star_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.star_mul_isFixed
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.star_mul_subset_prefixed
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.arden
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.mem_kpow_singleton
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.mem_star_singleton
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.part1
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.part1_freeMonoid
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkX_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkY_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.park_solves
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.park_least

@[expose] public section
