module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.mem_foldr_funInput
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_ii

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Union of input components of a finite set of function-space tokens. -/
def funInputUnion (s : Finset (FunToken A B)) : Finset α :=
  Multiset.foldr (fun p : FunToken A B => funion p.val.1) (∅ : Finset α) s.1

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


theorem funInputUnion.empty : funInputUnion A B (∅ : Finset (FunToken A B)) = ∅ :=
  rfl

end InfoSys
end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_funInputUnion {s : Finset (FunToken A B)} {x : α} :
    x ∈ funInputUnion A B s ↔ ∃ p ∈ s, x ∈ p.val.1 := by
  simpa [funInputUnion] using mem_foldr_funInput A B s.1 x

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem entSet_inputUnion_of_ent {u' : Finset α} {s : Finset (FunToken A B)}
    (h : ∀ q ∈ s, A.EntSet u' q.val.1) :
    A.EntSet u' (funInputUnion A B s) := by
  intro x hx
  rcases (mem_funInputUnion A B).1 hx with ⟨q, hq, hx'⟩
  exact h q hq x hx'

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem funInputUnion.con_of_ent {u' : Finset α} {s : Finset (FunToken A B)}
    (hu' : u' ∈ A.Con) (h : ∀ q ∈ s, A.EntSet u' q.val.1) :
    funInputUnion A B s ∈ A.Con :=
  A.con_subset (proposition_2_3_ii A hu' (entSet_inputUnion_of_ent A B h))
    (subset_funion_right _ _)

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem funInputUnion.funion (s t : Finset (FunToken A B)) :
    funInputUnion A B (s ∪' t) = funInputUnion A B s ∪' funInputUnion A B t := by
  ext x
  constructor
  · intro hx
    rcases (mem_funInputUnion A B).1 hx with ⟨p, hp, hx'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_funInputUnion A B).2 ⟨p, hp, hx'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_funInputUnion A B).2 ⟨p, hp, hx'⟩))
  · intro hx
    rcases mem_funion.mp hx with hx | hx
    · rcases (mem_funInputUnion A B).1 hx with ⟨p, hp, hx'⟩
      exact (mem_funInputUnion A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hx'⟩
    · rcases (mem_funInputUnion A B).1 hx with ⟨p, hp, hx'⟩
      exact (mem_funInputUnion A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hx'⟩

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem funInputUnion.singleton (p : FunToken A B) :
    funInputUnion A B {p} = p.val.1 := by
  ext x
  constructor
  · intro hx
    rcases (mem_funInputUnion A B).1 hx with ⟨q, hq, hx'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this
    exact hx'
  · intro hx
    exact (mem_funInputUnion A B).2 ⟨p, Finset.mem_singleton_self p, hx⟩

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem funInputUnion.insert (s : Finset (FunToken A B)) (p : FunToken A B) :
    funInputUnion A B (Insert.insert p s) = p.val.1 ∪' funInputUnion A B s := by
  have h : Insert.insert p s = ({p} : Finset (FunToken A B)) ∪' s := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_insert.mp hq with hqp | hq
      · exact mem_funion.mpr (Or.inl (hqp ▸ Finset.mem_singleton_self p))
      · exact mem_funion.mpr (Or.inr hq)
    · intro hq
      rcases mem_funion.mp hq with hq | hq
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hq))
      · exact Finset.mem_insert_of_mem hq
  rw [h, funInputUnion.funion, funInputUnion.singleton]

end InfoSys

end DomainTheory.InformationSystems
