/-ai
If every token of a finite set lies in the relation of an approximable map and the input union is consistent, then the map relates that input union to the output union.

The proof is by induction on the finite set. The empty unions are related by the empty relation. When a token is inserted, the induction hypothesis applies to the remainder because its input union is contained in the full input union. Monotonicity extends the token's relation and the remainder's relation from the union of the token's input with the remainder's input union, using reflexivity on each summand. The right-union law combines the two relations, and the input and output unions of an insertion are those combined unions.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

theorem rel_input_output_union (f : ApproximableMap A B)
    (s : Finset (FunToken A B))
    (hrel : ∀ q ∈ s, f.rel q.val.1 q.val.2)
    (hin : funInputUnion A B s ∈ A.Con) :
    f.rel (funInputUnion A B s) (funOutputUnion A B s) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [funInputUnion_empty, funOutputUnion_empty]
    exact f.empty_rel
  | insert q s' _hq ih =>
    have hrel' : ∀ r ∈ s', f.rel r.val.1 r.val.2 := fun r hr =>
      hrel r (Finset.mem_insert_of_mem hr)
    have hin' : funInputUnion A B s' ∈ A.Con :=
      A.con_subset hin (by
        rw [funInputUnion_insert]
        exact subset_funion_right _ _)
    have ih' := ih hrel' hin'
    have hqrel : f.rel q.val.1 q.val.2 := hrel q (Finset.mem_insert_self q s')
    have hinU : q.val.1 ∪' funInputUnion A B s' ∈ A.Con := by
      rwa [funInputUnion_insert] at hin
    have hEnt_q : A.EntSet (q.val.1 ∪' funInputUnion A B s') q.val.1 :=
      fun x hx => A.ent_refl hinU (subset_funion_left _ _ hx)
    have hEnt_s : A.EntSet (q.val.1 ∪' funInputUnion A B s') (funInputUnion A B s') :=
      fun x hx => A.ent_refl hinU (subset_funion_right _ _ hx)
    have h1 : f.rel (q.val.1 ∪' funInputUnion A B s') q.val.2 :=
      f.mono hqrel hEnt_q (proposition_2_3_iii B q.property.2) hinU q.property.2
    have h2 : f.rel (q.val.1 ∪' funInputUnion A B s') (funOutputUnion A B s') :=
      f.mono ih' hEnt_s (proposition_2_3_iii B (f.rel_cod ih')) hinU (f.rel_cod ih')
    rw [funInputUnion_insert, funOutputUnion_insert]
    exact f.union_right h1 h2

end InfoSys

end DomainTheory.InformationSystems
