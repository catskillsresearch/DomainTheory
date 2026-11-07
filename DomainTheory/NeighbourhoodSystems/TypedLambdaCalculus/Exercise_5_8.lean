module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.combinatoryComplete

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open CombinatoryComplete

/-- Scott's Exercise 5.8: every polynomial λ-term is realized by an I/K/S combinatory
term whose denotation agrees on every argument. -/
theorem example_508 :
    ∀ {X A : Dom} (t : Poly X A) (x : X.sys.Element),
      (toApproxMap (bracket t).denote).toElementMap x = t.denote x :=
  @bracket_spec

