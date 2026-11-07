module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.cAlgebra
public import DomainTheory.NeighbourhoodSystems.DomainEquations.cAlgebraGen

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open SeqDom SeqEqC BitDom Exercise419 SeqNegMerge
open Exercise617Gen

/-- Scott's Exercise 6.17: the initial `Tc`-algebra is unique. -/
theorem example_617 (B : TAlgebra Tc) (h' : AlgHom Calg B) : h' = descAlgHom B :=
  @descAlgHom_uniq B h'

/-- Scott's Exercise 6.17 (general `A`): `Cn A` and `CCn A` are isomorphic domains. -/
theorem example_617_gen (A : Type) [DecidableEq A] [Inhabited A] : Cn A ≅ᴰ CCn A :=
  @Cn_domain_equation A _ _

end DomainTheory.NeighbourhoodSystems
