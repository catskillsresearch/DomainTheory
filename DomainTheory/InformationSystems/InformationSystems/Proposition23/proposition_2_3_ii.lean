/-ai
If u is consistent and u set-entails v, then the constructive union of u with v is consistent.

The argument proves a stronger claim by induction on a finite set s contained in v: the constructive union of u with s is consistent. The empty case rewrites that union to u. In the inductive step, u entails the newly inserted token because the token lies in v. The inductive union is consistent, and cut moves the entailment from u to that union, since the union entails every member of u by reflexivity along the inclusion of u. The entailment-consistency axiom inserts the token, and distribution of constructive union over insertion rewrites the result. The original claim is the case where s is v.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Definition22
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.Basic
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.funion_insert

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Proposition 2.3(ii).** `u ⊢ v` implies `u ∪' v ∈ Con`. -/
theorem proposition_2_3_ii {u v : Finset α} (hu : u ∈ sys.Con) (h : sys.EntSet u v) :
    u ∪' v ∈ sys.Con := by
  have : ∀ s : Finset α, (∀ x ∈ s, x ∈ v) → u ∪' s ∈ sys.Con := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      -- foldr insert u 0 = u
      simpa [funion_empty_right] using hu
    · intro a t _ha ih hmem
      have hEnt_u_a : sys.Ent u a := h a (hmem a (Finset.mem_insert_self a t))
      have hut : u ∪' t ∈ sys.Con := ih fun x hx => hmem x (Finset.mem_insert_of_mem hx)
      have hEnt : sys.Ent (u ∪' t) a :=
        sys.ent_trans hut hu (fun y hy => sys.ent_refl hut (subset_funion_left u t hy))
          hEnt_u_a
      have hins : insert a (u ∪' t) ∈ sys.Con := sys.ent_con hEnt
      simpa [funion_insert] using hins
  exact this v fun _ hx => hx

end InfoSys
end DomainTheory.InformationSystems
