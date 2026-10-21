/-ai
Scott 1976, Theorem 4.6, the limit theorem. The Kleene iterates of a Scott-continuous retract-preserving map are retracts, and the Y combinator applied to the graph of the map is a retract, by the chain-union calculation.

The iterates are retracts by the iterate lemma. The fixed-point theorem for the Y combinator rewrites its application as the least fixed point. That fixed point equals the graph of its double application. The union of the retract iterates is a graph, so the graph of the application equals the fixed point. Extensionality of graphs and idempotence of the least-fixed-point application identify the graph of the double application with the graph of the single application, and these equalities are the retract equation.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.iUnion_retract_isGraph
public import DomainTheory.DataTypesAsLattices.Retracts.funOf_fix_idem

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.6 (The limit theorem).**
Kleene iterates of a retract-preserving continuous `F` are retracts, and
`Y(F)` is a retract by the chain-union calculation. -/
theorem theorem_4_6 {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a)) :
    (∀ n, IsRetract (iterateBot F n)) ∧
      IsRetract (funOf Ycomb (graph F)) := by
  refine ⟨iterates_areRetracts hret, ?_⟩
  have hY : funOf Ycomb (graph F) = fix F := theorem_2_5 hf
  rw [hY]
  change fix F = graph (fun x => funOf (fix F) (funOf (fix F) x))
  have hG : IsGraph (fix F) :=
    iUnion_retract_isGraph (iterates_areRetracts hret)
  have hgr : graph (funOf (fix F)) = fix F := (theorem_1_2_iii (fix F)).mpr hG
  have hidem' : graph (fun x => funOf (fix F) (funOf (fix F) x)) =
      graph (funOf (fix F)) :=
    graph_ext (fun x => funOf_fix_idem hf hret x)
  exact (hidem'.trans hgr).symm

end DomainTheory.DataTypesAsLattices
