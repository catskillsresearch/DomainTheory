/-ai
If evaluation is recursively enumerable on codes of computable presentations of the function space, the domain, and the codomain, then the relation of papplyEval on the corresponding power-domain codes is recursively enumerable.

The coded relation is rewritten by the equivalence between papplyEval on power-domain codes and the bounded quantifiers over decoded lists, and those quantifiers preserve recursive enumerability of the evaluation predicate.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.re_forallG_forallX_existsY
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise721.papplyEval_rel_Ypd_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}


/-- **Exercise 7.21 (the computability half) — `papply` is computable when `eval` is.** Stated at the
level of the `ℙ𝒟`-codes of Proposition 7.10: given that `eval` is recursively enumerable on codes
(`heval` — this is Theorem 7.5's `evalMap_isComputable` transported through `funPresentation`), the
relation `papplyEval.rel (Y_Φc)(Y_Ac)(Y_Bc)` is recursively enumerable in `⟨Φc, Ac, Bc⟩`. -/
theorem papplyEval_isComputable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (Pf : ComputablePresentation (funSpace V W)) (P : ComputablePresentation V)
    (Q : ComputablePresentation W)
    (heval : REPred (fun s => (eval V W).rel (Pf.X s.unpair.1)
      (P.X s.unpair.2.unpair.1) (Q.X s.unpair.2.unpair.2))) :
    REPred (fun w => (papplyEval V W).rel ((funSpace V W).Ypd Pf w.unpair.1)
      (V.Ypd P w.unpair.2.unpair.1) (W.Ypd Q w.unpair.2.unpair.2)) := by
  refine REPred.of_iff (fun w => ?_)
    (re_forallG_forallX_existsY
      (R := fun g x y => (eval V W).rel (Pf.X g) (P.X x) (Q.X y)) heval)
  exact papplyEval_rel_Ypd_iff Pf P Q

end DomainTheory.NeighbourhoodSystems
