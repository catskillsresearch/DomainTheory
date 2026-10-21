/-ai
Every neighbourhood of the sharp domain is related by the catamorphism to the master neighbourhood of the target.

The argument inducts on membership in the sharp domain. The master neighbourhood is the master clause. A zero embedding is the leaf clause, because the leaf map relates every neighbourhood in its domain to the master. A paired embedding is the node clause, because the inductive hypotheses relate the children to the master and the node map relates the master of the product, which is the product of the masters, to the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **Strictness in the relation: every `D^§`-neighbourhood folds to `Δ_E`.** This is why no separate
"top" clause is needed — `u`/`v` relate `Δ ↦ Δ`, so the master propagates through the tree. -/
theorem gRel_master : ∀ {W}, MemS D W → GRel u v W E.master := by
  intro W hW
  induction hW with
  | gamma => exact GRel.gamma rfl
  | @zero X hX =>
      exact GRel.leaf ((u.rel_iff_mem_principal hX).mpr (u.toElementMap _).master_mem)
  | @pair P Q _ _ ihP ihQ =>
      refine GRel.node ihP ihQ ?_
      have h := v.master_rel
      rwa [prod_master] at h

end Exercise717

end DomainTheory.NeighbourhoodSystems
