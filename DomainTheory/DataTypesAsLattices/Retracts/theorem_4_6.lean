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
    (hret : ∀ a, Retract a → Retract (F a)) :
    (∀ n, Retract (iterateBot F n)) ∧
      Retract (funOf Ycomb (graph F)) := by
  refine ⟨iterates_areRetracts hret, ?_⟩
  have hY : funOf Ycomb (graph F) = fix F := theorem_2_5 hf
  rw [hY]
  constructor
  change fix F = graph (fun x => funOf (fix F) (funOf (fix F) x))
  have hG : IsGraph (fix F) :=
    iUnion_retract_isGraph (iterates_areRetracts hret)
  have hgr : graph (funOf (fix F)) = fix F := (theorem_1_2_iii (fix F)).mpr hG
  have hidem' : graph (fun x => funOf (fix F) (funOf (fix F) x)) =
      graph (funOf (fix F)) :=
    graph_ext (fun x => funOf_fix_idem hf hret x)
  exact (hidem'.trans hgr).symm

end DomainTheory.DataTypesAsLattices
